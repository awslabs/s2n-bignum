(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The piece from loop5 (phase 4, the head of the copy loop): EmitCopy of    *)
(* the match (offset ip - candidate, length x), then at join12 (+0x368)      *)
(* emit_remainder (join2, phase 5) if ip + x >= ip_limit; otherwise the      *)
(* table updates at ip + x - 7 and - 4 (if ip + x > 7), - 3 and - 2          *)
(* (table2), - 2 and - 1 (table), the entry of table2 for Load64(ip + x)     *)
(* (c2, replaced by ip + x): FML E and loop5 if Load32 matches; else the     *)
(* entry of table for Load32(ip + x) (c1): FML D and loop5 if it matches,   *)
(* loop1 (phase 1) if not.                                                   *)
(*                                                                           *)
(* EmitCopy (L5_EMIT, loop5 .. join12) by its tags: L5_J15 (+0x520, one tag  *)
(* of 3 bytes), L5_J7 (+0x218, 2 or 3 bytes for a length up to 11), L5_J6    *)
(* (+0x208, 60 then the rest), L5_LOOP10 (+0x4f8, the tags of 64 bytes).     *)
(* The stores are 4 bytes each; their low 2 or 3 bytes are the tag (the      *)
(* output region of the contract is 5 bytes smaller than                     *)
(* MaxCompressedLength for that).                                            *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_loop5_spec.ml";;
needs "arm/proofs/snappy/events.ml";;
needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_lib.ml";;

(* ------------------------------------------------------------------------- *)
(* EmitCopy: the tags as numbers.                                            *)
(* ------------------------------------------------------------------------- *)

let L5_EC_SMALL = prove
 (`!off len. len <= 64 ==> snappy_emit_copy off len = snappy_emit_copy64 off len`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [snappy_emit_copy] THEN
  ASM_SIMP_TAC[ARITH_RULE `len <= 64 ==> ~(68 <= len) /\ ~(64 < len)`]);;

let L5_EC_MID = prove
 (`!off len. 64 < len /\ len < 68
             ==> snappy_emit_copy off len =
                 APPEND (snappy_emit_copy64 off 60)
                        (snappy_emit_copy off (len - 60))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [snappy_emit_copy] THEN
  ASM_SIMP_TAC[ARITH_RULE `len < 68 ==> ~(68 <= len)`] THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC L5_EC_SMALL THEN
  ASM_ARITH_TAC);;

let snappy_l5_reps = new_recursive_definition num_RECURSION
 `(snappy_l5_reps 0 (l:A list) = []) /\
  (snappy_l5_reps (SUC q) l = APPEND (snappy_l5_reps q l) l)`;;

let LENGTH_SNAPPY_L5_REPS = prove
 (`!q (l:A list). LENGTH(snappy_l5_reps q l) = q * LENGTH l`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[snappy_l5_reps; LENGTH; LENGTH_APPEND] THEN
  ARITH_TAC);;

let L5_REPS_COMM = prove
 (`!q (l:A list). APPEND l (snappy_l5_reps q l) = APPEND (snappy_l5_reps q l) l`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[snappy_l5_reps; APPEND; APPEND_NIL] THEN
  ASM_REWRITE_TAC[APPEND_ASSOC]);;

let L5_EC_REPS = prove
 (`!off q len. 64 * q + 4 <= len
               ==> snappy_emit_copy off len =
                   APPEND (snappy_l5_reps q (snappy_emit_copy64 off 64))
                          (snappy_emit_copy off (len - 64 * q))`,
  GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[snappy_l5_reps; APPEND; MULT_CLAUSES; SUB_0] THEN
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [snappy_emit_copy] THEN
  SUBGOAL_THEN `68 <= len` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `len - 64`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[APPEND_ASSOC; L5_REPS_COMM] THEN
  REWRITE_TAC[ARITH_RULE `len - 64 - 64 * q = len - (64 + 64 * q)`]);;

let L5_LENGTH_COPY64 = prove
 (`!off len. LENGTH(snappy_emit_copy64 off len) =
             if len < 12 /\ off < 2048 then 2 else 3`,
  REPEAT GEN_TAC THEN REWRITE_TAC[snappy_emit_copy64] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let L5_NUM_COPY1 = prove
 (`!off len. off < 2048 /\ 4 <= len /\ len < 12
             ==> num_of_bytelist(snappy_emit_copy64 off len) =
                 (32 * (off DIV 256) + 256 * off + 4 * len - 15) MOD 65536`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[snappy_emit_copy64] THEN
  REWRITE_TAC[num_of_bytelist; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPECL [`off:num`; `256`] DIVISION) THEN
  ABBREV_TAC `q = off DIV 256` THEN ABBREV_TAC `r = off MOD 256` THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  SUBGOAL_THEN `q < 8` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `off:num`
    then SUBST1_TAC th else failwith "") THEN
  SUBGOAL_THEN `32 * q + 256 * (q * 256 + r) + 4 * len - 15 =
                q * 65536 + (32 * q + 4 * len - 15 + 256 * r)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MOD_MULT_ADD] THEN
  SUBGOAL_THEN `(1 + 4 * (len - 4) + 32 * q) MOD 256 = 1 + 4 * (len - 4) + 32 * q /\
                r MOD 256 = r /\
                (32 * q + 4 * len - 15 + 256 * r) MOD 65536 =
                32 * q + 4 * len - 15 + 256 * r`
   (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let L5_NUM_COPY2 = prove
 (`!off len. off < 65536 /\ 1 <= len /\ len <= 64 /\ ~(len < 12 /\ off < 2048)
             ==> num_of_bytelist(snappy_emit_copy64 off len) =
                 256 * off + 4 * len - 2`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[snappy_emit_copy64] THEN
  REWRITE_TAC[num_of_bytelist; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPECL [`off:num`; `256`] DIVISION) THEN
  ABBREV_TAC `q = off DIV 256` THEN ABBREV_TAC `r = off MOD 256` THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  SUBGOAL_THEN `q < 256` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(2 + 4 * (len - 1)) MOD 256 = 2 + 4 * (len - 1) /\
                r MOD 256 = r /\ q MOD 256 = q`
   (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

(* The first k bytes of a 32-bit store.                                      *)

let L5_BYTES_OF_32 = prove
 (`!(m:(S,int64->byte)component) a v k s.
     read (m :> bytes32 a) s = word v /\ v < 2 EXP 32 /\ k <= 4
     ==> read (m :> bytes(a,k)) s = v MOD 2 EXP (8 * k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `read (bytes(a,4)) (read (m:(S,int64->byte)component) s) = v`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `val:int32->num` o
      check (fun th -> is_eq(concl th) && type_of(lhs(concl th)) = `:int32`)) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES32_WBYTES; VAL_READ_WBYTES;
                DIMINDEX_32; VAL_WORD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_SIMP_TAC[MOD_LT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:int64`; `4`; `k:num`;
                 `read (m:(S,int64->byte)component) s`] READ_BYTES_MOD) THEN
  ASM_SIMP_TAC[ARITH_RULE `k <= 4 ==> MIN 4 k = k`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN MESON_TAC[]);;

let L5_READ_BYTES_APPEND = prove
 (`!(m:(S,int64->byte)component) a k j x y s.
     read (m :> bytes(a,k)) s = x /\
     read (m :> bytes(word_add a (word k),j)) s = y
     ==> read (m :> bytes(a,k + j)) s = x + 2 EXP (8 * k) * y`,
  SIMP_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE]);;

let L5_AND224 = prove
 (`!x:int64. val x < 2048
       ==> val(word_and (word_zx (word_ushr x 3):int32) (word 224)) =
           32 * (val x DIV 256)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[BITBLAST_RULE
   `word_and (word_zx (word_ushr (x:int64) 3):int32) (word 224) =
    word_shl (word_and (word_zx (word_ushr x 8)) (word 7)) 5`] THEN
  SUBGOAL_THEN `word 7:int32 = word(2 EXP 3 - 1)` SUBST1_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV; REWRITE_TAC[WORD_AND_MASK_WORD]] THEN
  REWRITE_TAC[VAL_WORD_SHL; VAL_WORD; VAL_WORD_ZX_GEN; VAL_WORD_USHR;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `val(x:int64) DIV 256 < 8` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `x:int64` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_64] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `val(x:int64) MOD 18446744073709551616 = val x /\
                (val(x:int64) DIV 256) MOD 4294967296 = val x DIV 256 /\
                (val(x:int64) DIV 256) MOD 8 = val x DIV 256`
   (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  W(fun (asl,w) -> let l = lhs w in
    MP_TAC(SPECL [lhand l; rand l] MOD_LT)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* EmitCopy (loop5 .. join12).                                               *)
(* ------------------------------------------------------------------------- *)

let L5_EXEC = SNAPPY_CF2_GCC12_O2_EXEC;;

let L5_BYTES_OF_32_LT = prove
 (`!(m:(S,int64->byte)component) a v k s.
     read (m :> bytes32 a) s = word v /\ v < 2 EXP (8 * k) /\ k <= 4
     ==> read (m :> bytes(a,k)) s = v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(S,int64->byte)component`; `a:int64`; `v:num`; `k:num`;
                 `s:S`] L5_BYTES_OF_32) THEN
  SUBGOAL_THEN `v < 2 EXP 32` ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP (8 * k)` THEN ASM_REWRITE_TAC[LE_EXP] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT]);;

let L5_BYTES_OF_32_2 = prove
 (`!(m:(S,int64->byte)component) a v s.
     read (m :> bytes32 a) s = word v /\ v < 2 EXP 32
     ==> read (m :> bytes(a,2)) s = v MOD 65536`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(S,int64->byte)component`; `a:int64`; `v:num`; `2`;
                 `s:S`] L5_BYTES_OF_32) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

(* Replace the fact read c s = v (s the current state) by read c s = t,     *)
(* proving v = t with tac.                                                  *)

let L5_FIX_TAC (c:term) (t:term) (tac:tactic) : tactic = fun (asl,w) ->
  let s = rand w in
  let _,th = find (fun (_,th) -> is_eq(concl th) &&
      (match lhs(concl th) with
         Comb(Comb(Const("read",_),c'),s') -> c' = c && s' = s
       | _ -> false)) asl in
  let v = rhs(concl th) in
  if v = t then ALL_TAC (asl,w) else
  let eth = TAC_PROOF((asl,mk_eq(v,t)),tac) in
  (FIRST_X_ASSUM(fun th' -> if concl th' = concl th
                            then ASSUME_TAC(TRANS th' eth) else failwith ""))
  (asl,w);;

let L5_ADD_SUB_SWAP = WORD_RULE
  `!x y z:N word. word_add (word_sub x y) z = word_sub (word_add x z) y`;;

let L5_MOD_WRAP = prove
 (`!x n. n <= x /\ x < 2 * n ==> x MOD n = x - n`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN
  ASM_ARITH_TAC);;

(* CF2_MOD_ELIM_TAC, also for n <= x < 2 n.                                  *)

let L5_MOD_ELIM_TAC : tactic = fun (asl,w) ->
  let mods = setify (find_terms (fun t -> match t with
      Comb(Comb(Const("MOD",_),_),n) -> is_numeral n | _ -> false) w) in
  let ar tm = cf2_arith_prove (asl,tm)
      (MAP_EVERY (fun th -> ASSUME_TAC(ISPEC `src:byte list` th))
                 CF2_BOUND_RULES THEN ASM_ARITH_TAC) in
  let try_one t =
    let x,n = dest_binary "MOD" t in
    try MATCH_MP MOD_LT (ar (mk_binary "<" (x,n))) with Failure _ ->
    MATCH_MP L5_MOD_WRAP (ar (mk_conj(mk_binary "<=" (n,x),
                                     mk_binary "<" (x,mk_binary "*" (`2`,n))))) in
  match mapfilter try_one mods with
    [] -> failwith "L5_MOD_ELIM_TAC"
  | ths -> (REWRITE_TAC ths THEN CONV_TAC NUM_REDUCE_CONV) (asl,w);;

let L5_VAL_TAC (extra:thm list) =
  REWRITE_TAC[GSYM VAL_EQ] THEN REWRITE_TAC extra THEN
  REWRITE_TAC (VAL_WORD_SHL :: CF2_VAL_RULES) THEN REWRITE_TAC extra THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT L5_MOD_ELIM_TAC THEN
  REPEAT COND_CASES_TAC THEN REPEAT L5_MOD_ELIM_TAC THEN
  CF2_ARITH_TAC;;

let L5_WORD_TAC = FIRST [FML_WORD_EQ_TAC; L5_VAL_TAC []];;

let L5_FIX tm t = L5_FIX_TAC tm t L5_WORD_TAC;;

let l5_hyps =
 "aligned 4096 (word pc:int64) /\\ pc + libsnappy_size <= 2 EXP 64 /\\
  val (op:int64) + mx < 2 EXP 64 /\\
  nonoverlapping (op,mx) (word pc,libsnappy_rw + libsnappy_rw_size) /\\
  0 < off /\\ off < 65536";;

let l5_frame =
 "MAYCHANGE [PC; X1; X2; X4; X6; X7; X8; X14; X15; X17] ,,
  MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
  MAYCHANGE [memory :> bytes(op,mx)]";;

let l5_jframe =
 "MAYCHANGE [PC; X2; X4; X6; X7; X8; X14; X15; X17] ,,
  MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
  MAYCHANGE [memory :> bytes(op,mx)]";;

let l5_ev =
 "?e2. read events s = APPEND e2 e /\\
       memaccess_inbounds e2 [inp,LENGTH(src:byte list); op,mx] [op,mx]";;

(* The output after emit_copy off r at op + P.                               *)

let l5_out r =
 "read X2 s = word_add op (word(P + LENGTH(snappy_emit_copy off " ^ r ^ "))) /\\
  read (memory :> bytes(op,P + LENGTH(snappy_emit_copy off " ^ r ^ "))) s =
  v + 2 EXP (8 * P) * num_of_bytelist(snappy_emit_copy off " ^ r ^ ")";;

let l5_stmt (pre:string) (post:string) (extra:string) =
  parse_term
   ("!src inp op off r P mx v pc e. " ^ l5_hyps ^ " /\\ " ^ extra ^ "
     ==> ensures arm
          (\\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\\
               read (memory :> bytes(op,P)) s = v /\\
               read events s = e /\\ " ^ pre ^ ")
          (\\s. " ^ post ^ " /\\ " ^ l5_ev ^ ")
          (" ^ l5_jframe ^ ")");;

(* The facts of emit_copy off r for one tag of 2 or 3 bytes.                 *)

let L5_TAG_FACTS_TAC (r:term) =
  let ec = list_mk_icomb "snappy_emit_copy" [`off:num`; r] in
  let ec64 = list_mk_icomb "snappy_emit_copy64" [`off:num`; r] in
  SUBGOAL_THEN (mk_eq(ec,ec64)) SUBST1_TAC THENL
   [MATCH_MP_TAC L5_EC_SMALL THEN CF2_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[L5_LENGTH_COPY64] THEN
  W(fun (asl,w) ->
    let c = mk_conj(mk_binary "<" (r,`12`),`off < 2048`) in
    try let cth = TAC_PROOF((asl,c),CONJ_TAC THEN CF2_ARITH_TAC) in
        let h = list_mk_conj [`off < 2048`; mk_binary "<=" (`4`,r);
                              mk_binary "<" (r,`12`)] in
        let nth = MP (SPECL [`off:num`; r] L5_NUM_COPY1)
                     (TAC_PROOF((asl,h),REPEAT CONJ_TAC THEN CF2_ARITH_TAC)) in
        REWRITE_TAC[cth; nth]
    with Failure _ ->
        let cth = TAC_PROOF((asl,mk_neg c),
          REWRITE_TAC[DE_MORGAN_THM; NOT_LT] THEN CF2_ARITH_TAC) in
        let h = list_mk_conj [`off < 65536`; mk_binary "<=" (`1`,r);
                              mk_binary "<=" (r,`64`); mk_neg c] in
        let nth = MP (SPECL [`off:num`; r] L5_NUM_COPY2)
                     (TAC_PROOF((asl,h),REPEAT CONJ_TAC THEN
                        TRY(ACCEPT_TAC cth) THEN CF2_ARITH_TAC)) in
        REWRITE_TAC[REWRITE_RULE[] cth; nth]);;

(* The goal read (memory :> bytes(op,P + k)) s = v + 2 EXP (8 * P) * n from *)
(* bytes(op,P) = v and the 32-bit store of n (or of a number whose low k    *)
(* bytes are n) at op + P.                                                   *)

let L5_APPEND_TAC =
  MATCH_MP_TAC L5_READ_BYTES_APPEND THEN CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST [MATCH_MP_TAC L5_BYTES_OF_32_LT THEN
           REPEAT CONJ_TAC THENL
            [FIRST_ASSUM ACCEPT_TAC; CONV_TAC NUM_REDUCE_CONV THEN CF2_ARITH_TAC;
             CONV_TAC NUM_REDUCE_CONV];
           MATCH_MP_TAC L5_BYTES_OF_32_2 THEN
           CONJ_TAC THENL
            [FIRST_ASSUM ACCEPT_TAC; CONV_TAC NUM_REDUCE_CONV THEN CF2_ARITH_TAC]]];;

let L5_FIN_TAC =
  BSTEP_FINAL_TAC THEN REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  TRY(MEMSAFE_EVENTS_TAC THEN NO_TAC);;

(* The goals of a post after a tag lemma: the register goal by its fact,    *)
(* the bytes goal by the fact of the bytes at op of another length (with the *)
(* abbreviations v' and P' expanded, the powers of 2 normalized).            *)

let L5_REG_GOAL_TAC : tactic = fun (asl,w) ->
  let l,_ = dest_eq w in
  let th = snd(find (fun (_,th) -> is_eq(concl th) && lhs(concl th) = l) asl) in
  (GEN_REWRITE_TAC LAND_CONV [th] THEN L5_WORD_TAC) (asl,w);;

let L5_EXP_NORM_CONV =
  DEPTH_CONV (fun t -> match t with
      Comb(Comb(Const("EXP",_),_),e) when not(is_numeral e) ->
        CHANGED_CONV (RAND_CONV NUM_NORMALIZE_CONV) t
    | _ -> failwith "L5_EXP_NORM_CONV");;

let L5_BYTES_GOAL_TAC : tactic = fun (asl,w) ->
  let l,_ = dest_eq w in
  let s = rand l in
  let blen t = rand(rand(rand(rand(rator t)))) and baddr t = lhand(rand(rand(rand(rator t)))) in
  let th = snd(find (fun (_,th) -> is_eq(concl th) &&
     (try let t = lhs(concl th) in
          rand t = s && baddr t = `op:int64` &&
          not(blen t = `P:num`) && type_of(rhs(concl th)) = `:num`
      with Failure _ -> false)) asl) in
  let n' = blen(lhs(concl th)) and n = blen l in
  let eq = TAC_PROOF((asl,mk_eq(n,n')),CF2_ARITH_TAC) in
  (GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV o RAND_CONV o RAND_CONV o
                    RAND_CONV) [eq] THEN
   GEN_REWRITE_TAC LAND_CONV [th] THEN
   TRY(EXPAND_TAC "v'") THEN TRY(EXPAND_TAC "P'") THEN
   CONV_TAC L5_EXP_NORM_CONV THEN REWRITE_TAC[EXP_ADD] THEN
   CONV_TAC L5_EXP_NORM_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
   CONV_TAC NUM_RING) (asl,w);;

(* join15 (+0x520): a tag of 3 bytes for 12 <= r <= 64.                     *)

let L5_J15 = prove
 (l5_stmt
   "read PC s = word(pc + 16384) /\\
    read X6 s = word(256 * off) /\\ read X4 s = word r /\\
    read X2 s = word_add op (word P)"
   ("read PC s = word(pc + 15944) /\\ " ^ l5_out "r")
   "12 <= r /\\ r <= 64 /\\ P + 4 <= mx",
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ARM_BSTEP_TAC L5_EXEC (1--3) THEN
  L5_FIX `memory :> bytes32 (word_add op (word P))`
    `word(256 * off + 4 * r - 2):int32` THEN
  L5_FIX `X2` `word_add op (word(P + 3)):int64` THEN
  ARM_BSTEP_TAC L5_EXEC (4--4) THEN
  L5_TAG_FACTS_TAC `r:num` THEN
  L5_FIN_TAC THEN L5_APPEND_TAC);;

(* join7 (+0x218): a tag of 2 bytes (off < 2048) or 3 bytes for r <= 11, at *)
(* X8 = op + P.                                                               *)

let L5_J7 = prove
 (l5_stmt
   "read PC s = word(pc + 15608) /\\
    read X6 s = word(256 * off) /\\ read X7 s = word r /\\
    read X14 s = word off /\\ read X8 s = word_add op (word P)"
   ("read PC s = word(pc + 15944) /\\ " ^ l5_out "r")
   "4 <= r /\\ r <= 11 /\\ P + 4 <= mx",
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ARM_BSTEP_TAC L5_EXEC (1--3) THEN
  L5_FIX `X7` `word(256 * off + 4 * r):int64` THEN
  FML_BRANCH_TAC `off < 2048` THENL
   [ARM_BSTEP_TAC L5_EXEC (4--6) THEN
    MP_TAC(SPEC `word off:int64` L5_AND224) THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `off MOD 18446744073709551616 = off` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN CF2_ARITH_TAC; ALL_TAC] THEN
    ANTS_TAC THENL [CF2_ARITH_TAC; DISCH_TAC] THEN
    L5_FIX_TAC `X4` `word(32 * (off DIV 256)):int64`
      (FIRST_X_ASSUM(fun th -> if is_eq(concl th) && is_comb(lhs(concl th)) &&
          rator(lhs(concl th)) = `val:int32->num` then
          L5_VAL_TAC [th] else failwith "")) THEN
    ARM_BSTEP_TAC L5_EXEC (7--11) THEN
    L5_FIX `memory :> bytes32 (word_add op (word P))`
      `word(32 * (off DIV 256) + 256 * off + 4 * r - 15):int32` THEN
    L5_FIX `X2` `word_add op (word(P + 2)):int64` THEN
    ARM_BSTEP_TAC L5_EXEC (12--12) THEN
    L5_TAG_FACTS_TAC `r:num` THEN
    L5_FIN_TAC THEN L5_APPEND_TAC;
    ARM_BSTEP_TAC L5_EXEC (4--7) THEN
    L5_FIX `memory :> bytes32 (word_add op (word P))`
      `word(256 * off + 4 * r - 2):int32` THEN
    L5_FIX `X2` `word_add op (word(P + 3)):int64` THEN
    ARM_BSTEP_TAC L5_EXEC (8--8) THEN
    L5_TAG_FACTS_TAC `r:num` THEN
    L5_FIN_TAC THEN L5_APPEND_TAC]);;

(* join6 (+0x208): the tag of 60 bytes, then join7 for r - 60 (5..7).       *)

let L5_J6 = prove
 (l5_stmt
   "read PC s = word(pc + 15592) /\\
    read X6 s = word(256 * off) /\\ read X7 s = word r /\\
    read X14 s = word off /\\ read X2 s = word_add op (word P)"
   ("read PC s = word(pc + 15944) /\\ " ^ l5_out "r")
   "65 <= r /\\ r <= 67 /\\ P + 7 <= mx",
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ARM_BSTEP_TAC L5_EXEC (1--4) THEN
  L5_FIX `memory :> bytes32 (word_add op (word P))`
    `word(256 * off + 238):int32` THEN
  L5_FIX `X8` `word_add op (word(P + 3)):int64` THEN
  L5_FIX `X7` `word(r - 60):int64` THEN
  SUBGOAL_THEN `read (memory :> bytes(op,P + 3)) s4 =
                v + 2 EXP (8 * P) * (256 * off + 238)` ASSUME_TAC THENL
   [L5_APPEND_TAC; ALL_TAC] THEN
  FML_CALL_TAC L5_J7 [`r - 60`,"r"; `P + 3`,"P";
     `v + 2 EXP (8 * P) * (256 * off + 238)`,"v"] "s5" THEN
  MP_TAC(SPECL [`off:num`; `r:num`] L5_EC_MID) THEN
  ANTS_TAC THENL [CF2_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`off:num`; `60`] L5_NUM_COPY2) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN CF2_ARITH_TAC; DISCH_TAC] THEN
  REWRITE_TAC[LENGTH_APPEND; SNAPPY_NUM_OF_BYTELIST_APPEND; L5_LENGTH_COPY64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  L5_FIN_TAC THEN FIRST [L5_REG_GOAL_TAC; L5_BYTES_GOAL_TAC]);;

(* loop10 (+0x4f8): q tags of 64 bytes, i of them written.                  *)

let L5_LOOP10 = prove
 (parse_term
   ("!src inp op off q i P mx v pc e. " ^ l5_hyps ^ " /\\
     i < q /\\ P + 3 * q + 1 <= mx
     ==> ensures arm
          (\\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\\
               read PC s = word(pc + 16344) /\\
               read X2 s = word_add op (word(P + 3 * i)) /\\
               read X8 s = word_add op (word(P + 3 * q)) /\\
               read X17 s = word(256 * off + 254) /\\
               read (memory :> bytes(op,P + 3 * i)) s =
               v + 2 EXP (8 * P) *
                   num_of_bytelist(snappy_l5_reps i (snappy_emit_copy64 off 64)) /\\
               read events s = e)
          (\\s. read PC s = word(pc + 16356) /\\
               read X2 s = word_add op (word(P + 3 * q)) /\\
               read X8 s = word_add op (word(P + 3 * q)) /\\
               read (memory :> bytes(op,P + 3 * q)) s =
               v + 2 EXP (8 * P) *
                   num_of_bytelist(snappy_l5_reps q (snappy_emit_copy64 off 64)) /\\
               " ^ l5_ev ^ ")
          (MAYCHANGE [PC; X2] ,, MAYCHANGE [NF; ZF; CF; VF] ,,
           MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(op,mx)])"),
  REPEAT GEN_TAC THEN SPEC_TAC(`e:(uarch_event)list`,`e:(uarch_event)list`) THEN
  WF_INDUCT_TAC `q - i:num` THEN GEN_TAC THEN
  STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `P + 3 * i + 4 <= mx` ASSUME_TAC THENL
   [CF2_ARITH_TAC; ALL_TAC] THEN
  ARM_BSTEP_TAC L5_EXEC (1--1) THEN
  L5_FIX `memory :> bytes32 (word_add op (word(P + 3 * i)))`
    `word(256 * off + 254):int32` THEN
  L5_FIX `X2` `word_add op (word(P + 3 * (i + 1))):int64` THEN
  MP_TAC(SPECL [`off:num`; `64`] L5_NUM_COPY2) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN CF2_ARITH_TAC;
                  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `read (memory :> bytes(op,P + 3 * (i + 1))) s1 =
    v + 2 EXP (8 * P) *
        num_of_bytelist(snappy_l5_reps (i + 1) (snappy_emit_copy64 off 64))`
   ASSUME_TAC THENL
   [REWRITE_TAC[GSYM ADD1; snappy_l5_reps; SNAPPY_NUM_OF_BYTELIST_APPEND;
                LENGTH_SNAPPY_L5_REPS; L5_LENGTH_COPY64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `P + 3 * SUC i = (P + 3 * i) + 3`] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(v + 2 EXP (8 * P) *
                 num_of_bytelist(snappy_l5_reps i (snappy_emit_copy64 off 64))) +
                2 EXP (8 * (P + 3 * i)) * (256 * off + 254)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC L5_READ_BYTES_APPEND THEN CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC L5_BYTES_OF_32_LT THEN REPEAT CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC; CONV_TAC NUM_REDUCE_CONV THEN CF2_ARITH_TAC;
          CONV_TAC NUM_REDUCE_CONV]];
      CONV_TAC L5_EXP_NORM_CONV THEN REWRITE_TAC[EXP_ADD] THEN
      CONV_TAC L5_EXP_NORM_CONV THEN CONV_TAC NUM_RING];
    ALL_TAC] THEN
  ARM_BSTEP_TAC L5_EXEC (2--3) THEN
  FML_BRANCH_TAC `i + 1 = q` THENL
   [L5_FIN_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `i + 1 = q`]) THEN
    TRY(FIRST_ASSUM ACCEPT_TAC);
    FML_IH_TAC [`i + 1`,"i"] "s4" THEN L5_FIN_TAC]);;

(* EmitCopy from loop5 to join12.                                            *)

let l5_emit_post =
 "read PC s = word(pc + 15944) /\\
  read X1 s = word_add inp (word(ip + x)) /\\
  read X2 s = word_add op (word(P + LENGTH(snappy_emit_copy (ip - c) x))) /\\
  read (memory :> bytes(op,P + LENGTH(snappy_emit_copy (ip - c) x))) s =
  v + 2 EXP (8 * P) * num_of_bytelist(snappy_emit_copy (ip - c) x)";;

let L5_EMIT_STMT = parse_term
 ("!src inp op ip c x P mx v pc e.
     aligned 4096 (word pc:int64) /\\ pc + libsnappy_size <= 2 EXP 64 /\\
     val (op:int64) + mx < 2 EXP 64 /\\
     nonoverlapping (op,mx) (word pc,libsnappy_rw + libsnappy_rw_size) /\\
     c < ip /\\ ip < 65536 /\\ 4 <= x /\\ x < 65536 /\\
     P + LENGTH(snappy_emit_copy (ip - c) x) + 2 <= mx
     ==> ensures arm
          (\\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\\
               read PC s = word(pc + 15552) /\\
               read X8 s = word_add inp (word ip) /\\
               read X14 s = word_add inp (word c) /\\
               read X4 s = word x /\\
               read X2 s = word_add op (word P) /\\
               read (memory :> bytes(op,P)) s = v /\\
               read events s = e)
          (\\s. " ^ l5_emit_post ^ " /\\ " ^ l5_ev ^ ")
          (" ^ l5_frame ^ ")");;

(* The lengths of the tags: 2 or 3, at least 5 for 65..67.                   *)

let L5_LENGTH_EC = prove
 (`!off r. 4 <= r /\ r <= 64
           ==> 2 <= LENGTH(snappy_emit_copy off r) /\
               LENGTH(snappy_emit_copy off r) <= 3`,
  SIMP_TAC[L5_EC_SMALL; L5_LENGTH_COPY64] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ARITH_TAC);;

let L5_LENGTH_EC_MID = prove
 (`!off r. 64 < r /\ r < 68 ==> 5 <= LENGTH(snappy_emit_copy off r)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[L5_EC_MID; LENGTH_APPEND] THEN
  ASM_SIMP_TAC[L5_EC_SMALL; ARITH_RULE `r < 68 ==> r - 60 <= 64`] THEN
  REWRITE_TAC[L5_LENGTH_COPY64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT COND_CASES_TAC THEN ARITH_TAC);;

let L5_EC_REPS_REWRITE_TAC =
  FIRST_ASSUM(fun th -> if is_eq(concl th) &&
                           lhs(concl th) = `snappy_emit_copy off x`
                        then REWRITE_TAC[th] else failwith "");;

let l5_vq = `v + 2 EXP (8 * P) *
  num_of_bytelist(snappy_l5_reps q (snappy_emit_copy64 off 64))`;;

let L5_EMIT = prove
 (L5_EMIT_STMT,
  REPEAT STRIP_TAC THEN ABBREV_TAC `off = ip - c` THEN
  SUBGOAL_THEN `0 < off /\ off < 65536` STRIP_ASSUME_TAC THENL
   [CF2_ARITH_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_BSTEP_TAC L5_EXEC (1--1) THEN
  L5_FIX `X14` `word off:int64` THEN
  ARM_BSTEP_TAC L5_EXEC (2--2) THEN
  L5_FIX `X7` `word x:int64` THEN
  ARM_BSTEP_TAC L5_EXEC (3--4) THEN
  L5_FIX `X1` `word_add inp (word(ip + x)):int64` THEN
  L5_FIX `X6` `word(256 * off):int64` THEN
  ARM_BSTEP_TAC L5_EXEC (5--6) THEN
  FML_BRANCH_TAC `x <= 11` THENL
   [(* x <= 11 *)
    MP_TAC(SPECL [`off:num`; `x:num`] L5_LENGTH_EC) THEN
    ANTS_TAC THENL [CF2_ARITH_TAC; STRIP_TAC] THEN
    ARM_BSTEP_TAC L5_EXEC (7--9) THEN
    L5_FIX `X6` `word(256 * off + 4 * x):int64` THEN
    FML_BRANCH_TAC `off < 2048` THENL
     [ARM_BSTEP_TAC L5_EXEC (10--12) THEN
      MP_TAC(SPEC `word off:int64` L5_AND224) THEN
      REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
      SUBGOAL_THEN `off MOD 18446744073709551616 = off` SUBST1_TAC THENL
       [MATCH_MP_TAC MOD_LT THEN CF2_ARITH_TAC; ALL_TAC] THEN
      ANTS_TAC THENL [CF2_ARITH_TAC; DISCH_TAC] THEN
      L5_FIX_TAC `X4` `word(32 * (off DIV 256)):int64`
        (FIRST_X_ASSUM(fun th -> if is_eq(concl th) && is_comb(lhs(concl th)) &&
            rator(lhs(concl th)) = `val:int32->num` then
            L5_VAL_TAC [th] else failwith "")) THEN
      ARM_BSTEP_TAC L5_EXEC (13--16) THEN
      L5_FIX `memory :> bytes32 (word_add op (word P))`
        `word(32 * (off DIV 256) + 256 * off + 4 * x - 15):int32` THEN
      ARM_BSTEP_TAC L5_EXEC (17--17) THEN
      L5_FIX `X2` `word_add op (word(P + 2)):int64` THEN
      L5_TAG_FACTS_TAC `x:num` THEN
      L5_FIN_TAC THEN L5_APPEND_TAC;
      ARM_BSTEP_TAC L5_EXEC (10--12) THEN
      L5_FIX `memory :> bytes32 (word_add op (word P))`
        `word(256 * off + 4 * x - 2):int32` THEN
      ARM_BSTEP_TAC L5_EXEC (13--13) THEN
      L5_FIX `X2` `word_add op (word(P + 3)):int64` THEN
      L5_TAG_FACTS_TAC `x:num` THEN
      L5_FIN_TAC THEN L5_APPEND_TAC];
    ARM_BSTEP_TAC L5_EXEC (7--8) THEN
    FML_BRANCH_TAC `67 < x` THENL
     [(* x >= 68: loop10, then the rest r = x - 64 q *)
      ABBREV_TAC `q = (x - 68) DIV 64 + 1` THEN
      SUBGOAL_THEN `1 <= q /\ 64 * q + 4 <= x /\ x - 64 * q < 68 /\
                    4 <= x - 64 * q` STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "q" THEN MP_TAC(SPECL [`x - 68`; `64`] DIVISION) THEN
        CF2_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`off:num`; `q:num`; `x:num`] L5_EC_REPS) THEN
      ANTS_TAC THENL [CF2_ARITH_TAC; DISCH_TAC] THEN
      ABBREV_TAC `r = x - 64 * q` THEN
      SUBGOAL_THEN `P + 3 * q + LENGTH(snappy_emit_copy off r) + 2 <= mx`
       ASSUME_TAC THENL
       [UNDISCH_TAC `P + LENGTH(snappy_emit_copy off x) + 2 <= mx` THEN
        ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_SNAPPY_L5_REPS; L5_LENGTH_COPY64] THEN
        CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
        ALL_TAC] THEN
      ARM_BSTEP_TAC L5_EXEC (9--13) THEN
      L5_FIX `X15` `word((x - 68) DIV 64):int64` THEN
      L5_FIX `X17` `word(256 * off + 254):int64` THEN
      L5_FIX `X4` `word(3 * q):int64` THEN
      ARM_BSTEP_TAC L5_EXEC (14--14) THEN
      L5_FIX `X8` `word_add op (word(P + 3 * q)):int64` THEN
      SUBGOAL_THEN
       `read (memory :> bytes(op,P)) s14 =
        v + 2 EXP (8 * P) *
            num_of_bytelist(snappy_l5_reps 0 (snappy_emit_copy64 off 64))`
       ASSUME_TAC THENL
       [REWRITE_TAC[snappy_l5_reps; num_of_bytelist; MULT_CLAUSES; ADD_CLAUSES] THEN
        FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      FML_CALL_TAC L5_LOOP10 [`0`,"i"] "s15" THEN
      ARM_BSTEP_TAC L5_EXEC (16--17) THEN
      L5_FIX `X7` `word r:int64` THEN
      ARM_BSTEP_TAC L5_EXEC (18--19) THEN
      FML_BRANCH_TAC `64 < r` THENL
       [MP_TAC(SPECL [`off:num`; `r:num`] L5_LENGTH_EC_MID) THEN
        ANTS_TAC THENL [CF2_ARITH_TAC; DISCH_TAC] THEN
        FML_CALL_TAC L5_J6 [`P + 3 * q`,"P"; l5_vq,"v"] "s20";
        ARM_BSTEP_TAC L5_EXEC (20--22) THEN
        MP_TAC(SPECL [`off:num`; `r:num`] L5_LENGTH_EC) THEN
        ANTS_TAC THENL [CF2_ARITH_TAC; STRIP_TAC] THEN
        L5_FIX `X4` `word r:int64` THEN
        FML_BRANCH_TAC `r <= 11` THENL
         [FML_CALL_TAC L5_J7 [`P + 3 * q`,"P"; l5_vq,"v"] "s23";
          FML_CALL_TAC L5_J15 [`P + 3 * q`,"P"; l5_vq,"v"] "s23"]] THEN
      L5_EC_REPS_REWRITE_TAC THEN
      REWRITE_TAC[LENGTH_APPEND; LENGTH_SNAPPY_L5_REPS; L5_LENGTH_COPY64;
                  SNAPPY_NUM_OF_BYTELIST_APPEND] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      L5_FIN_TAC THEN
      FIRST [L5_REG_GOAL_TAC; L5_BYTES_GOAL_TAC];
      (* 12 <= x <= 67 *)
      ARM_BSTEP_TAC L5_EXEC (9--10) THEN
      FML_BRANCH_TAC `x <= 64` THENL
       [MP_TAC(SPECL [`off:num`; `x:num`] L5_LENGTH_EC) THEN
        ANTS_TAC THENL [CF2_ARITH_TAC; STRIP_TAC] THEN
        FML_CALL_TAC L5_J15 [`x:num`,"r"] "s11" THEN L5_FIN_TAC;
        MP_TAC(SPECL [`off:num`; `x:num`] L5_LENGTH_EC_MID) THEN
        ANTS_TAC THENL [CF2_ARITH_TAC; DISCH_TAC] THEN
        FML_CALL_TAC L5_J6 [`x:num`,"r"] "s11" THEN L5_FIN_TAC]]]);;

(* Tactics of the loop2 and join5 pieces, as in their proofs. *)

let CF2_L5A_TB_TAC (t:term) (e:term) =
  FIRST_ASSUM(fun th -> match concl th with
      Comb(Comb(Const("snappy_tbound",_),t'),_) when t' = t ->
        ASSUME_TAC(SPEC e (MATCH_MP SNAPPY_TBOUND_LOOKUP th))
    | _ -> failwith "CF2_L5A_TB_TAC");;

let CF2_L5A_ZX16 = prove
 (`!v. v < 65536 ==> word_zx (word v:int16):int64 = word v`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_16;
              DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `v < 65536 ==> v < 18446744073709551616`]);;

let CF2_L5A_ZX16_TAC (v:term) : tactic = fun (asl,w) ->
  let lt = mk_binary "<" (v,`65536`) in
  let lth = TAC_PROOF((asl,lt),CF2_ARITH_TAC) in
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP CF2_L5A_ZX16 lth]) (asl,w);;

(* e < ts for a hash entry e, as an assumption.                         *)
let CF2_L5A_HASH_LT_TAC (e:term) : tactic = fun (asl,w) ->
  let lt = mk_binary "<" (e,`ts:num`) in
  let th = TAC_PROOF((asl,lt),
    ASM_SIMP_TAC[SNAPPY_HASH4_LT; SNAPPY_HASH8_LT;
                 ARITH_RULE `128 <= ts ==> ~(ts = 0)`]) in
  ASSUME_TAC th (asl,w);;

let CF2_L5A_MOD32 = CONV_RULE NUM_REDUCE_CONV SNAPPY_LOAD64_MOD32;;

(* CF2_WORD_EQ_TAC with the arithmetic on the numerical assumptions only.  *)
let CF2_L5A_WORD_EQ_TAC =
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  FIRST
   [REFL_TAC;
    AP_TERM_TAC THEN AP_TERM_TAC THEN CF2_ARITH_TAC;
    REWRITE_TAC[GSYM VAL_EQ] THEN REWRITE_TAC CF2_VAL_RULES THEN
    CONV_TAC NUM_REDUCE_CONV THEN REPEAT CF2_MOD_ELIM_TAC THEN
    CF2_ARITH_TAC];;

let CF2_L5A_CONTAINED_REFL = prove
 (`!x:int64 n. contained (x,n) (x,n)`,
  REWRITE_TAC[contained; contained_modulo] THEN MESON_TAC[CONG_REFL]);;

let CF2_L5A_INB_LIFT = prove
 (`!e (x:int64) n r1 w.
     memaccess_inbounds e [x,n] [] ==> memaccess_inbounds e (CONS (x,n) r1) w`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MEMACCESS_INBOUNDS_CONTAINED THEN
  REWRITE_TAC[ALL; EX; CF2_L5A_CONTAINED_REFL]);;

(* Lift memaccess_inbounds x [inp,LENGTH src] [] to the regions of the piece. *)
let CF2_L5A_INB_LIFT_TAC =
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
                     CF2_L5A_INB_LIFT) th)
    | _ -> th);;

(* Go through a contract th (an assume_spec theorem hyps ==> ensures ...),  *)
(* with its events variable e set to the current events and insts.          *)
let CF2_L5A_CALL_TAC (th:thm) (args:term list) sname : tactic =
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
   CF2_L5A_INB_LIFT_TAC) (asl,w);;

let CF2_L5A_DIVPOS = prove
 (`!sk. 512 <= sk ==> 1 <= sk DIV 512`,
  SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN ARITH_TAC);;

let CF2_L5A_MLEN_TAC (a:term) (b:term) =
  ASSUME_TAC(SPECL [`src:byte list`; a; b] SNAPPY_MATCH_LENGTH);;

(* Join the parts of a table into the whole fact at the current state.     *)
let CF2_L5A_JOIN_TAC (tab:term) (t:term) (e:term) (v:term) : tactic = fun (asl,w) ->
  let s = rand w in
  let tm = subst [tab,`tab:int64`; t,`t:num->num`; e,`e:num`; v,`v:num`; s,`s:armstate`]
    `read (memory :> bytes(tab:int64,2 * ts)) (s:armstate) =
     snappy_tval ts (snappy_tupd (t:num->num) e v)` in
  (SUBGOAL_THEN tm ASSUME_TAC THENL [CF2_TABLE_JOIN_TAC; ALL_TAC]) (asl,w);;

(* The 32-bit hash of the data as the code computes it, in the facts.       *)
let CF2_L5A_HASH4_TAC (d:term) : tactic = fun (asl,w) ->
  let th0 = SPECL [`ts:num`; d] SNAPPY_HASH4_WORD in
  let hth = TAC_PROOF((asl,lhand(concl th0)),
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REWRITE_TAC[SNAPPY_LOAD64_BOUND]) in
  RULE_ASSUM_TAC(REWRITE_RULE[MP th0 hth; SNAPPY_LOAD64_MOD32]) (asl,w);;

(* bstep rewrites branch conditions with the static assumptions: orient     *)
(* ts = snappy_table_size .. DIV 2 the other way, so that ts stays.          *)
let CF2_L5A_TS_FLIP_TAC =
  FIRST_X_ASSUM(fun th -> match concl th with
      Comb(Comb(Const("=",_),Var("ts",_)),_) -> ASSUME_TAC(SYM th)
    | _ -> failwith "CF2_L5A_TS_FLIP_TAC");;

let CF2_L5A_ZXZX = prove
 (`!n. n < 4294967296 ==> word_zx (word_zx (word n:int64):int32):int64 = word n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
              DIMINDEX_64] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN
  UNDISCH_TAC `n < 4294967296` THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `n < 4294967296 ==> n < 18446744073709551616`]);;

(* The instance for 2 * h, h a hash entry (h < ts as an assumption).       *)
let CF2_L5A_ZXZX_RULE (asl:(string*thm) list) (h:term) =
  let n = mk_comb(mk_comb(`( * ):num->num->num`,`2`),h) in
  let lt = mk_comb(mk_comb(`(<):num->num->bool`,n),`4294967296`) in
  MP (SPEC n CF2_L5A_ZXZX) (TAC_PROOF((asl,lt),CF2_ARITH_TAC));;

let CF2_L5A_AND16 = BITBLAST_RULE
 `word_zx (word_and (y:int32) (word 65535)):int16 = word_zx y`;;

let CF2_L5A_ENTRY = prove
 (`!x:int64 v. v < 65536
      ==> word_zx (word_and (word_zx (word_sub (word_add x (word v)) x):int32)
                            (word 65535)):int16 = word v`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[CF2_L5A_AND16; WORD_RULE `word_sub (word_add x y) x:int64 = y`] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_16;
              DIMINDEX_32; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* The stored entry ip (or ip + 1): its word form in the facts.            *)
let CF2_L5A_ENTRY_TAC (v:term) : tactic = fun (asl,w) ->
  let lt = mk_comb(mk_comb(`(<):num->num->bool`,v),`65536`) in
  let lth = TAC_PROOF((asl,lt),CF2_ARITH_TAC) in
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP (SPEC `inp:int64` CF2_L5A_ENTRY) lth]) (asl,w);;

(* The target, with the remaining conjuncts of the state at the point left  *)
(* as goals (to be closed by the caller).                                    *)
let CF2_L5A_TARGET_TAC (pt:term) (st:term) (mids:term list) =
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

let CF2_L5A_OUT_BOUND = prove
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
let CF2_L5A_OUT_TAC : tactic = fun (asl,w) ->
  let th = SPECL [`LENGTH(src:byte list)`; `ne:num`] CF2_L5A_OUT_BOUND in
  let hth = TAC_PROOF((asl,lhand(concl th)), CONJ_TAC THEN CF2_ARITH_TAC) in
  ASSUME_TAC (MP th hth) (asl,w);;

(* Replace the value of a register (or other component) fact by an equal     *)
(* word new, proved by CF2_WORD_EQ_TAC.                                     *)
let CF2_L5A_REG_EQ_TAC (c:term) (nw:term) : tactic = fun (asl,w) ->
  let s = rand w in
  let th = snd(find (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c'),s')),_)
        -> s' = s && c' = c | _ -> false) asl) in
  let old = rhs(concl th) in
  let eth = TAC_PROOF((asl,mk_eq(old,nw)),CF2_L5A_WORD_EQ_TAC) in
  (FIRST_X_ASSUM(fun th' -> if concl th' = concl th then
     ASSUME_TAC(TRANS th' eth) else failwith "")) (asl,w);;

let CF2_L5A_CLOSE_TAC =
  FIRST [REWRITE_TAC[snappy_cf2_events] THEN MEMSAFE_EVENTS_TAC THEN NO_TAC;
         CF2_ARITH_TAC; CF2_L5A_WORD_EQ_TAC THEN NO_TAC;
         CF2_TABLE_JOIN_TAC THEN NO_TAC];;

(* CF2_BRANCH_TAC with the case used as cond = T (not as a rewrite of its    *)
(* left side, which may occur inside its right side).                        *)
let CF2_L5A_BRANCH_TAC ?(extra=[]) (cond:term) : tactic = fun (asl,w) ->
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

let CF2_L5A_HASH8_32 = prove
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
let CF2_L5A_TBUPD_TAC (t:term) (e:term) (v:term) (b:term) : tactic = fun (asl,w) ->
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

let CF2_L5A_HASH8_32_TAC (d:term) : tactic = fun (asl,w) ->
  let th0 = SPECL [`ts:num`; d] CF2_L5A_HASH8_32 in
  let hth = TAC_PROOF((asl,lhand(concl th0)),
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REWRITE_TAC[SNAPPY_LOAD64_BOUND]) in
  RULE_ASSUM_TAC(REWRITE_RULE[MP th0 hth]) (asl,w);;

let CF2_L5A_HASH8_TAC (d:term) : tactic = fun (asl,w) ->
  let th0 = SPECL [`ts:num`; d] SNAPPY_HASH8_WORD in
  let hth = TAC_PROOF((asl,lhand(concl th0)),
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REWRITE_TAC[SNAPPY_LOAD64_BOUND]) in
  RULE_ASSUM_TAC(REWRITE_RULE[MP th0 hth]) (asl,w);;

let CF2_L5A_CLOSE2_TAC =
  FIRST [REWRITE_TAC[snappy_cf2_events] THEN MEMSAFE_EVENTS_TAC THEN NO_TAC;
         CF2_ARITH_TAC;
         CF2_L5A_WORD_EQ_TAC THEN NO_TAC;
         W(fun (asl,w) -> ASM_SIMP_TAC[SNAPPY_HASH8_WORD; SNAPPY_LOAD64_BOUND])
           THEN NO_TAC];;

let CF2_L5A_CLOSE3_TAC = CF2_L5A_CLOSE_TAC ORELSE CF2_L5A_CLOSE2_TAC;;

let CF2_L5B_MOD_ADD_MUL = prove
 (`!x y n. (x + n * y) MOD n = x MOD n`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[MOD_MULT_ADD]);;

let CF2_L5B_READ_BYTES_PREFIX = prove
 (`!(m:(S,int64->byte)component) a k j (l:byte list) p s.
     read (m :> bytes(a,k)) s = num_of_bytelist(SUB_LIST(p,k) l) /\ j <= k
     ==> read (m :> bytes(a,j)) s = num_of_bytelist(SUB_LIST(p,j) l)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. x MOD 2 EXP (8 * j)`) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[SNAPPY_NUM_OF_BYTELIST_SUB_LIST; MOD_MOD_EXP_MIN] THEN
  REWRITE_TAC[ARITH_RULE `MIN (8 * (j + d)) (8 * j) = 8 * j`] THEN
  SIMP_TAC[CF2_L5B_MOD_ADD_MUL; MOD_LT; READ_BYTES_BOUND]);;

let CF2_L5B_LOAD64_PAIR = prove
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

let CF2_L5B_BYTES64_PAIR = prove
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

let CF2_L5B_SUB_LIST_ADD = prove
 (`!(l:byte list) p a b.
     p + a + b <= LENGTH l
     ==> num_of_bytelist(SUB_LIST(p,a + b) l) =
         num_of_bytelist(SUB_LIST(p,a) l) +
         2 EXP (8 * a) * num_of_bytelist(SUB_LIST(p + a,b) l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SNAPPY_NUM_OF_BYTELIST_SUB_LIST] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; GSYM DIV_DIV] THEN
  REWRITE_TAC[MOD_MULT_MOD] THEN ARITH_TAC);;

let CF2_L5B_IVAL_WORD64 = prove
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

let CF2_L5B_IVAL_WORD32 = prove
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

let CF2_L5B_WORD_SX32 = prove
 (`!k. k < 2 EXP 31 ==> word_sx(word k:int32):int64 = word k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_sx] THEN
  ASM_SIMP_TAC[CF2_L5B_IVAL_WORD32; GSYM WORD_IWORD]);;

let CF2_L5B_WSUB_IWORD = prove
 (`!a b. word_sub (word a) (word b):N word = iword(&a - &b)`,
  REWRITE_TAC[IWORD_INT_SUB; GSYM WORD_IWORD]);;

let CF2_L5B_HASH4_WORD = prove
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

let CF2_L5B_ZXZX = prove
 (`!k. k < 2 EXP 32 ==> word_zx(word_zx(word k:int64):int32):int64 = word k`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  SUBGOAL_THEN `k MOD 2 EXP 32 = k /\ k MOD 2 EXP 64 = k`
   (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `k < 2 EXP 32` THEN
  ARITH_TAC);;

let CF2_L5B_IVAL_SUB32 = prove
 (`!a b. a < 2 EXP 31 /\ b < 2 EXP 31
         ==> ival(word_sub (word a) (word b):int32) = &a - &b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CF2_L5B_WSUB_IWORD] THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_POW]) THEN
  RULE_ASSUM_TAC(CONV_RULE INT_REDUCE_CONV) THEN ASM_INT_ARITH_TAC);;

let CF2_L5B_WORD_SUB_LE = prove
 (`!x y. y <= x ==> word_sub (word x) (word y):N word = word(x - y)`,
  SIMP_TAC[WORD_SUB]);;

let CF2_L5B_ZX_SUB1 = prove
 (`!k. 1 <= k /\ k < 2 EXP 32
       ==> word_zx(word_sub (word_zx(word k:int64):int32) (word 1)):int64 =
           word(k - 1)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[WORD_ZX_WORD_SIMPLE; DIMINDEX_32; DIMINDEX_64; ARITH] THEN
  ASM_SIMP_TAC[CF2_L5B_WORD_SUB_LE] THEN
  REWRITE_TAC[WORD_ZX_WORD; DIMINDEX_32] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let CF2_L5B_LIT2 = prove
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

let CF2_L5B_ZX32 = prove
 (`!k. word_zx (word k:int64):int32 = word k`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64;
              MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

(* The signed comparison k <= 59 of the 32-bit word k.                      *)

(* The number of bytes of the length of a long literal, from clz.           *)

let CF2_L5B_CLZ_DIV8 = prove
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

let CF2_L5B_ISHR_SMALL = prove
 (`!k n. k < 2 EXP 31 ==> word_ishr (word k:int32) n = word(k DIV 2 EXP n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ishr] THEN
  ASM_SIMP_TAC[CF2_L5B_IVAL_WORD32] THEN
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_DIV; GSYM WORD_IWORD]);;

let CF2_L5B_CLZ_SMALL = prove
 (`!x:int32. word_clz x < 2 EXP 31`,
  GEN_TAC THEN MP_TAC(ISPEC `x:int32` WORD_CLZ_LE_DIMINDEX) THEN
  REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* loop11 of EmitLiteral: 16 bytes at a time from next_emit to op + P,     *)
(* until op + P + len (so up to 15 bytes more than the literal, in the      *)
(* output region and from the input).                                       *)

(* Tactics of the join5 piece *)

let CF2_L5B_WSUB = WORD_RULE `word_sub (word_add a b) a:int64 = b`;;

let CF2_L5B_AND65535 = prove
 (`!x:int32. word_and x (word 65535) = word(val x MOD 65536)`,
  GEN_TAC THEN MP_TAC(ISPECL [`x:int32`; `16`] (CONJUNCT1 WORD_AND_MASK_WORD)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

(* Replace the fact read c s = v (s the current state) by read c s = t,     *)
(* proving v = t with tac.                                                  *)

let CF2_L5B_FIX_TAC (c:term) (t:term) (tac:tactic) : tactic = fun (asl,w) ->
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

let CF2_L5B_VAL_TAC =
  REWRITE_TAC[CF2_L5B_WSUB; CF2_L5B_AND65535] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN REWRITE_TAC CF2_VAL_RULES THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT CF2_MOD_ELIM_TAC THEN
  REWRITE_TAC CF2_VAL_RULES THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT CF2_MOD_ELIM_TAC THEN CF2_ARITH_TAC;;

let CF2_L5B_HASH8_TAC =
  FIRST_ASSUM(fun pth -> if concl pth = `snappy_pow2 ts`
    then ASM_SIMP_TAC[SNAPPY_HASH8_WORD; SNAPPY_LOAD64_BOUND; pth]
    else failwith "CF2_L5B_HASH8_TAC");;

(* e < ts and 2 * e + 2 <= 2 * ts for a hash e, for the orthogonality      *)
(* of its entry from the other regions.                                      *)

let CF2_L5B_ENTRY_BOUND_TAC (e:term) : tactic =
  SUBGOAL_THEN (mk_conj(mk_binary "<" (e,`ts:num`),
     mk_binary "<=" (mk_binary "+" (mk_binary "*" (`2`,e),`2`),`2 * ts`)))
   STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `e < ts ==> e < ts /\ 2 * e + 2 <= 2 * ts`) THEN
    ASM_SIMP_TAC[SNAPPY_HASH4_LT; SNAPPY_HASH8_LT; ARITH_RULE
      `128 <= ts ==> ~(ts = 0)`];
    ALL_TAC];;

(* CF2_TABLE_SPLIT_TAC with the table bound for an updated table (eta).  *)

let CF2_L5B_TABLE_SPLIT_TAC (a:term) (e:term) : tactic = fun (asl,w) ->
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

let CF2_L5B_STORE_TAC ?(rewrites=[]) (tbl:term) (e:term) (v:term) (m,n) : tactic =
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
    (CF2_L5B_ENTRY_BOUND_TAC e THEN CF2_L5B_TABLE_SPLIT_TAC tbl e THEN
     ARM_BSTEP_TAC ~rewrites SNAPPY_CF2_GCC12_O2_EXEC (m--n) THEN
     SUBGOAL_THEN goal ASSUME_TAC THENL [CF2_TABLE_JOIN_TAC; ALL_TAC] THEN
     DISCARD_ASSUMPTIONS_TAC is_part THEN
     CF2_L5A_TBUPD_TAC t e v `(ip + x) - 1`) (asl,w);;

let CF2_L5B_SYM tm = ISPECL [lhand tm; rand tm] WORD_ADD_SYM;;

let CF2_L5B_HASH4_TAC =
  FIRST_ASSUM(fun pth -> if concl pth = `snappy_pow2 ts`
    then ASM_SIMP_TAC[CF2_L5B_HASH4_WORD; SNAPPY_LOAD32_BOUND; pth]
    else failwith "CF2_L5B_HASH4_TAC");;

(* A branch on data, the condition proved equivalent to cond by tac.       *)

let CF2_L5B_BRANCH_TAC (cond:term) (tac:tactic) : tactic = fun (asl,w) ->
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

let CF2_L5B_OUTBOUND_TAC =
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

let CF2_L5B_BOUNDS_TAC (tms:term list) =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL [CF2_ARITH_TAC; ALL_TAC]) tms;;

(* The value of a component in the current state.                          *)

let cf2_l5b_value (c:term) (asl,w) =
  let s = rand w in
  rhs(concl(snd(find (fun (_,th) -> is_eq(concl th) &&
     (match lhs(concl th) with
        Comb(Comb(Const("read",_),c'),s') -> c' = c && s' = s
      | _ -> false)) asl)));;

(* signed conditions *)
let CF2_L5B_SCOND_TAC (ths:thm list) =
  SIMP_TAC[WORD_SUB_0; WORD_ZX_WORD_SIMPLE; DIMINDEX_32; DIMINDEX_64; ARITH] THEN
  REWRITE_TAC ths THEN
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; GSYM VAL_EQ] THEN
  REWRITE_TAC CF2_VAL_RULES THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT CF2_MOD_ELIM_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_LE] THEN
  W(fun (asl,w) -> ACCEPT_TAC(cf2_arith_prove (asl,w)
    (RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_LT;
                                 GSYM INT_OF_NUM_LE]) THEN
     ASM_INT_ARITH_TAC)));;

(* ------------------------------------------------------------------------- *)
(* The piece from loop5.                                                     *)
(* ------------------------------------------------------------------------- *)

let L5_IVAL_SUB64 = prove
 (`!a b. a < 2 EXP 63 /\ b < 2 EXP 63
         ==> ival(word_sub (word a) (word b):int64) = &a - &b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CF2_L5B_WSUB_IWORD] THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_POW]) THEN
  RULE_ASSUM_TAC(CONV_RULE INT_REDUCE_CONV) THEN ASM_INT_ARITH_TAC);;

let L5_NEG_ADDR = prove
 (`!(a:int64) p k. k <= p /\ k <= 2 EXP 64
     ==> word_add (word_add a (word p)) (word(2 EXP 64 - k)) =
         word_add a (word(p - k))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `p + 2 EXP 64 - k = (p - k) + 1 * 2 EXP 64` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[MOD_MULT_ADD]]);;

(* The read of the input at ip + x - k (the address x1 - k) at the current  *)
(* state, of a 64-bit, 32-bit or 8-bit load (lemma).                         *)

let L5_NREAD_TAC (lemma:thm) (k:int) : tactic = fun (asl,w) ->
  let s = rand w in
  let kt = mk_small_numeral k in
  let p = mk_binary "-" (`ip + x`,kt) in
  let neg = mk_comb(`word:num->int64`,
                    mk_numeral(Num.sub_num (Num.power_num (Num.num_of_int 2)
                                 (Num.num_of_int 64)) (Num.num_of_int k))) in
  let addr = mk_icomb(mk_icomb(`word_add:int64->int64->int64`,
                               `word_add (inp:int64) (word(ip + x))`),neg) in
  let th0 = ISPECL [`memory:(armstate,int64->byte)component`; `inp:int64`;
                    `src:byte list`; p; s] lemma in
  let c = rand(concl th0) in
  let l = lhs c in
  let tm = mk_eq(subst [addr,rand(rand(rand(rator l)))] l, rhs c) in
  let th = TAC_PROOF((asl,tm),
    SUBGOAL_THEN (mk_eq(addr,mk_icomb(`word_add (inp:int64)`,
                                      mk_comb(`word:num->int64`,p))))
     SUBST1_TAC THENL
     [MP_TAC(SPECL [`inp:int64`; `ip + x`; kt] L5_NEG_ADDR) THEN
      CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN MATCH_MP_TAC THEN
      CF2_ARITH_TAC;
      MATCH_MP_TAC lemma THEN CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC; CF2_ARITH_TAC]]) in
  let aeq = mk_eq(addr,mk_icomb(`word_add (inp:int64)`,mk_comb(`word:num->int64`,p))) in
  let ath = TAC_PROOF((asl,aeq),
     MP_TAC(SPECL [`inp:int64`; `ip + x`; kt] L5_NEG_ADDR) THEN
     CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN MATCH_MP_TAC THEN
     CF2_ARITH_TAC) in
  (ASSUME_TAC th THEN
   (if exists (fun (_,t) -> concl t = aeq) asl then ALL_TAC
    else ASSUME_TAC ath)) (asl,w);;

(* The events with the addresses x1 - k as inp + (ip + x - k).               *)

let L5_EVNORM_TAC : tactic = fun (asl,w) ->
  let eqs = map snd (filter (fun (_,th) -> is_eq(concl th) &&
      (match lhs(concl th) with
         Comb(Comb(Const("word_add",_),Comb(Comb(Const("word_add",_),i),_)),_)
           -> i = `inp:int64`
       | _ -> false)) asl) in
  RULE_ASSUM_TAC(fun th -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("events",_)),_)),_)
        -> REWRITE_RULE eqs th
    | _ -> th) (asl,w);;

let cf2_l5b_ival_facts asl =
  map snd (filter (fun (_,th) ->
    can (find_term ((=) `ival:int64->int`)) (concl th) ||
    can (find_term ((=) `ival:int32->int`)) (concl th)) asl);;

let L5_IPX = `ip + x`;;
let L5_OUT' = `APPEND out (snappy_emit_copy (ip - c) x)`;;

let l5_h8 k = subst [mk_small_numeral k,`k:num`]
  `snappy_hash8 ts (snappy_load64 src ((ip + x) - k))`;;
let l5_h4 k = subst [mk_small_numeral k,`k:num`]
  `snappy_hash4 ts (snappy_load32 src ((ip + x) - k))`;;
let l5_v k = subst [mk_small_numeral k,`k:num`] `(ip + x) - k`;;

let L5_EE = `snappy_hash8 ts (snappy_load64 src (ip + x))`;;
let L5_FF = `snappy_hash4 ts (snappy_load32 src (ip + x))`;;

let l5_tupd t e v = list_mk_icomb "snappy_tupd" [t;e;v];;

let L5_T2A_GT = l5_tupd (l5_tupd `t2:num->num` (l5_h8 7) (l5_v 7)) (l5_h8 4) (l5_v 4);;
let l5_t2b t2a = l5_tupd (l5_tupd t2a (l5_h8 3) (l5_v 3)) (l5_h8 2) (l5_v 2);;
let L5_T1A = l5_tupd (l5_tupd `t1:num->num` (l5_h4 2) (l5_v 2)) (l5_h4 1) (l5_v 1);;

(* The output bound and the output after EmitCopy.                          *)

let L5_OUTBOUND_TAC =
  MP_TAC(SPECL [`src:byte list`; `out:byte list`; `ip:num`; `c:num`; `x:num`]
    SNAPPY_COPY_STEP_MATCHES) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
                  CF2_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `LENGTH(out:byte list) + LENGTH(snappy_emit_copy (ip - c) x) + 2 <=
    snappy_max_compressed_length (LENGTH(src:byte list)) - 5`
  ASSUME_TAC THENL
   [MP_TAC(SPEC `LENGTH(src:byte list)` SNAPPY_MAX_COMPRESSED_LENGTH_32) THEN
    ANTS_TAC THENL [CF2_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `(ip + x) DIV 30 <= LENGTH(src:byte list) DIV 6` MP_TAC THENL
     [TRANS_TAC LE_TRANS `LENGTH(src:byte list) DIV 30` THEN CONJ_TAC THENL
       [MATCH_MP_TAC DIV_MONO THEN CF2_ARITH_TAC;
        MATCH_MP_TAC DIV_MONO2 THEN ARITH_TAC];
      FIRST_X_ASSUM(MP_TAC o check (fun th ->
        can (find_term ((=) `LENGTH:byte list->num`)) (concl th) &&
        can (find_term ((=) `APPEND:byte list->byte list->byte list`)) (concl th) &&
        is_binary "<=" (concl th))) THEN
      REWRITE_TAC[LENGTH_APPEND] THEN CF2_ARITH_TAC];
    ALL_TAC];;

let L5_OUT_TAC (s:term) =
  SUBGOAL_THEN (subst [s,`s:armstate`]
   `read (memory :> bytes(op,LENGTH(APPEND out (snappy_emit_copy (ip - c) x))))
         (s:armstate) =
    num_of_bytelist(APPEND out (snappy_emit_copy (ip - c) x))`)
  ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND; SNAPPY_NUM_OF_BYTELIST_APPEND] THEN
    FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  L5_FIX_TAC `X2`
   `word_add op (word(LENGTH(APPEND out (snappy_emit_copy (ip - c) x)))):int64`
   (REWRITE_TAC[LENGTH_APPEND]);;

(* The targets.                                                              *)

let L5_CLOSE_TAC =
  FIRST [REWRITE_TAC[LENGTH_APPEND; SNAPPY_NUM_OF_BYTELIST_APPEND] THEN
         FIRST_ASSUM ACCEPT_TAC;
         CF2_L5A_INB_LIFT_TAC THEN L5_EVNORM_TAC THEN
         REWRITE_TAC[snappy_cf2_events] THEN
         (* the events by base and offset (events.ml), else as before    *)
         (SNAPPY_EVENTS_TAC ORELSE MEMSAFE_EVENTS_TAC) THEN NO_TAC;
         CF2_L5A_CLOSE3_TAC];;

(* CF2_L5A_BRANCH_TAC also for a condition b of the form ~cond.             *)

let L5_BRANCH_TAC (cond:term) : tactic = fun (asl,w) ->
  let s = rand w in
  let is_pc th = match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),s')),r)
        -> s' = s && is_cond r
    | _ -> false in
  let pcth = snd(find (is_pc o snd) asl) in
  let b,_ = dest_cond(rhs(concl pcth)) in
  let eqth = try TAC_PROOF((asl,mk_iff(b,cond)),CF2_COND_EQ_TAC [])
             with Failure _ ->
               TAC_PROOF((asl,mk_iff(b,mk_neg cond)),
                 REWRITE_TAC[] THEN CF2_COND_EQ_TAC []) in
  (ASM_CASES_TAC cond THEN
   FIRST_X_ASSUM(fun cth ->
     let cth' = if is_neg(concl cth) then EQF_INTRO cth
                else EQT_INTRO cth in
     FIRST_X_ASSUM(fun th -> if concl th = concl pcth then
        ASSUME_TAC(REWRITE_RULE[eqth; cth'] th) else failwith "") THEN
     ASSUME_TAC cth)) (asl,w);;

let l5_sname k = "s" ^ string_of_int k;;

let L5_H8FIX (r:term) (k:int) =
  CF2_L5B_FIX_TAC r (mk_comb(`word:num->int64`,mk_binary "*" (`2`,l5_h8 k)))
    CF2_L5B_HASH8_TAC;;

let L5_H4FIX (r:term) (k:int) =
  CF2_L5B_FIX_TAC r (mk_comb(`word:num->int64`,mk_binary "*" (`2`,l5_h4 k)))
    CF2_L5B_HASH4_TAC;;

let L5_VFIX (r:term) (k:int) =
  CF2_L5B_FIX_TAC r (mk_comb(`word:num->int64`,l5_v k)) CF2_L5B_VAL_TAC;;

let L5_T2STORE (k:int) (n:int) =
  CF2_L5B_STORE_TAC
   ~rewrites:[CF2_L5B_SYM (mk_icomb(mk_icomb(`word_add:int64->int64->int64`,
       mk_comb(`word:num->int64`,mk_binary "*" (`2`,l5_h8 k))),`table2:int64`))]
   `table2:int64` (l5_h8 k) (l5_v k) (n,n);;

let L5_T1STORE (k:int) (n:int) : tactic = fun (asl,w) ->
  let e = l5_h4 k in
  let lt = mk_binary "<" (mk_binary "*" (`2`,e),`4294967296`) in
  let lth = TAC_PROOF((asl,lt),
    MATCH_MP_TAC(ARITH_RULE `e < 16384 ==> 2 * e < 4294967296`) THEN
    MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `ts:num` THEN
    ASM_SIMP_TAC[SNAPPY_HASH4_LT; ARITH_RULE `128 <= ts ==> ~(ts = 0)`]) in
  let zth = MATCH_MP CF2_L5A_ZXZX lth in
  CF2_L5B_STORE_TAC ~rewrites:[zth] `table:int64` e (l5_v k) (n,n) (asl,w);;

(* The table updates when ip + x > 7 (+0x380 .. +0x3b4), steps 8..21.      *)

let L5_GT7_TAC =
  L5_NREAD_TAC SNAPPY_READ_LOAD64 7 THEN
  ARM_BSTEP_TAC L5_EXEC (8--16) THEN
  L5_VFIX `X8` 7 THEN L5_VFIX `X7` 4 THEN L5_H8FIX `X4` 7 THEN
  L5_T2STORE 7 17 THEN
  L5_NREAD_TAC SNAPPY_READ_LOAD64 4 THEN
  ARM_BSTEP_TAC L5_EXEC (18--20) THEN L5_H8FIX `X4` 4 THEN
  L5_T2STORE 4 21;;

(* The updates from join13 (+0x3b8) at step k with table2 t2a, then the     *)
(* checks for a next match: FML E with c2 (table2), loop1, or FML D with c1  *)
(* (table); both FML cases then join18 and loop5.                            *)

let l5_st4 c len t1 t2 =
  list_mk_icomb "SnappyCState"
   [`4`; L5_IPX; `ne:num`; `sk:num`; c; len; t1; t2; L5_OUT'];;

let l5_st1 t1 t2 =
  list_mk_icomb "SnappyCState"
   [`1`; L5_IPX; `ne:num`; `sk:num`; `c:num`; `x:num`; t1; t2; L5_OUT'];;

let l5_len c =
  mk_binary "+"
   (list_mk_icomb "snappy_match_length"
     [`src:byte list`; mk_binary "+" (c,`4`); `(ip + x) + 4`],`4`);;

(* After the call of FML D or E (at state k): join18, loop5.                 *)

let L5_NEXT_TAC (k:int) (c:term) (t1:term) (t2:term) =
  CF2_L5A_MLEN_TAC (mk_binary "+" (c,`4`)) `(ip + x) + 4` THEN
  ARM_BSTEP_TAC L5_EXEC ((k+1)--(k+3)) THEN
  CF2_L5B_FIX_TAC `X4` (mk_comb(`word:num->int64`,l5_len c)) CF2_L5B_VAL_TAC THEN
  BSTEP_FINAL_TAC THEN
  CF2_L5A_TARGET_TAC `CompressFragmentDoubleHash_loop5:num`
    (l5_st4 c (l5_len c) t1 t2) [] THEN
  L5_CLOSE_TAC;;

let L5_J13_TAC (k:int) (t2a:term) =
  let t2b = l5_t2b t2a in
  let c2 = mk_comb(t2b,L5_EE) in
  let t2c = l5_tupd t2b L5_EE L5_IPX in
  let c1 = mk_comb(L5_T1A,L5_FF) in
  let t1b = l5_tupd L5_T1A L5_FF L5_IPX in
  L5_NREAD_TAC SNAPPY_READ_LOAD64 3 THEN
  ARM_BSTEP_TAC L5_EXEC (k--(k+6)) THEN
  L5_VFIX `X14` 3 THEN L5_VFIX `X4` 2 THEN L5_VFIX `X8` 1 THEN
  L5_H8FIX `X7` 3 THEN L5_T2STORE 3 (k+7) THEN
  L5_NREAD_TAC SNAPPY_READ_LOAD64 2 THEN
  ARM_BSTEP_TAC L5_EXEC ((k+8)--(k+10)) THEN
  L5_H8FIX `X7` 2 THEN L5_T2STORE 2 (k+11) THEN
  L5_NREAD_TAC SNAPPY_READ_LOAD32 2 THEN
  ARM_BSTEP_TAC L5_EXEC ((k+12)--(k+14)) THEN
  L5_H4FIX `X7` 2 THEN L5_T1STORE 2 (k+15) THEN
  L5_NREAD_TAC SNAPPY_READ_LOAD32 1 THEN
  ARM_BSTEP_TAC L5_EXEC ((k+16)--(k+18)) THEN
  L5_H4FIX `X4` 1 THEN L5_T1STORE 1 (k+19) THEN
  CF2_INPUT_TAC SNAPPY_READ_LOAD64 `ip + x` THEN
  ARM_BSTEP_TAC L5_EXEC ((k+20)--(k+23)) THEN
  CF2_L5A_HASH8_32_TAC `snappy_load64 src (ip + x)` THEN
  (* table2 at e2 = hash8(Load64(ip + x)): c2, then ip + x *)
  CF2_L5A_HASH_LT_TAC L5_EE THEN
  CF2_TABLE_SPLIT_TAC `table2:int64` L5_EE THEN
  W(fun (asl,w) ->
    ARM_BSTEP_TAC ~rewrites:[CF2_L5A_ZXZX_RULE asl L5_EE]
      L5_EXEC ((k+24)--(k+24))) THEN
  CF2_L5A_TB_TAC t2b L5_EE THEN
  CF2_L5A_ZX16_TAC c2 THEN
  W(fun (asl,w) ->
    ARM_BSTEP_TAC ~rewrites:[CF2_L5A_ZXZX_RULE asl L5_EE]
      L5_EXEC ((k+25)--(k+26))) THEN
  CF2_L5A_JOIN_TAC `table2:int64` t2b L5_EE L5_IPX THEN
  CF2_INPUT_TAC SNAPPY_READ_LOAD32 `ip + x` THEN
  CF2_INPUT_TAC SNAPPY_READ_LOAD32 c2 THEN
  ARM_BSTEP_TAC L5_EXEC ((k+27)--(k+30)) THEN
  CF2_L5A_BRANCH_TAC
   (mk_eq(`snappy_load32 src (ip + x)`,mk_icomb(`snappy_load32 src`,c2))) THENL
   [CF2_L5A_CALL_TAC SNAPPY_CF2_GCC12_O2_FML_E
     [`src:byte list`; `inp:int64`; L5_IPX; c2; `pc:num`] (l5_sname(k+31)) THEN
    L5_NEXT_TAC (k+31) c2 L5_T1A t2c;
    ARM_BSTEP_TAC L5_EXEC ((k+31)--(k+32)) THEN
    CF2_L5B_FIX_TAC `X4` (mk_comb(`word:num->int64`,mk_binary "*" (`2`,L5_FF)))
      CF2_L5B_HASH4_TAC THEN
    CF2_L5A_HASH_LT_TAC L5_FF THEN
    CF2_TABLE_SPLIT_TAC `table:int64` L5_FF THEN
    W(fun (asl,w) ->
      ARM_BSTEP_TAC ~rewrites:[CF2_L5A_ZXZX_RULE asl L5_FF]
        L5_EXEC ((k+33)--(k+33))) THEN
    CF2_L5A_TB_TAC L5_T1A L5_FF THEN
    CF2_L5A_ZX16_TAC c1 THEN
    W(fun (asl,w) ->
      ARM_BSTEP_TAC ~rewrites:[CF2_L5A_ZXZX_RULE asl L5_FF]
        L5_EXEC ((k+34)--(k+35))) THEN
    CF2_L5A_JOIN_TAC `table:int64` L5_T1A L5_FF L5_IPX THEN
    CF2_INPUT_TAC SNAPPY_READ_LOAD32 `ip + x` THEN
    CF2_INPUT_TAC SNAPPY_READ_LOAD32 c1 THEN
    ARM_BSTEP_TAC L5_EXEC ((k+36)--(k+39)) THEN
    L5_BRANCH_TAC
     (mk_eq(`snappy_load32 src (ip + x)`,mk_icomb(`snappy_load32 src`,c1))) THENL
     [CF2_L5A_CALL_TAC SNAPPY_CF2_GCC12_O2_FML_D
       [`src:byte list`; `inp:int64`; L5_IPX; c1; `pc:num`] (l5_sname(k+40)) THEN
      L5_NEXT_TAC (k+40) c1 t1b t2c;
      BSTEP_FINAL_TAC THEN
      CF2_L5A_TARGET_TAC `CompressFragmentDoubleHash_loop1:num`
        (l5_st1 t1b t2c) [] THEN
      L5_CLOSE_TAC]];;

let L5_ST5 = list_mk_icomb "SnappyCState"
  [`5`; L5_IPX; `ne:num`; `sk:num`; `c:num`; `x:num`; `t1:num->num`;
   `t2:num->num`; L5_OUT'];;

let SNAPPY_CF2_GCC12_O2_LOOP5 = prove
 (SNAPPY_CF2_GCC12_O2_LOOP5_STMT,
  CF2_PIECE_START_TAC THEN CF2_INIT_TAC THEN CF2_L5A_TS_FLIP_TAC THEN
  L5_OUTBOUND_TAC THEN
  FML_CALL_TAC L5_EMIT
   [`LENGTH(out:byte list)`,"P";
    `snappy_max_compressed_length (LENGTH(src:byte list)) - 5`,"mx";
    `num_of_bytelist(out:byte list)`,"v"] "s1" THEN
  L5_OUT_TAC `s1:armstate` THEN
  ARM_BSTEP_TAC L5_EXEC (2--3) THEN
  CF2_L5A_BRANCH_TAC `LENGTH(src:byte list) - 15 <= ip + x` THENL
   [ARM_BSTEP_TAC L5_EXEC (4--4) THEN BSTEP_FINAL_TAC THEN
    CF2_L5A_TARGET_TAC `CompressFragmentDoubleHash_join2:num` L5_ST5 [] THEN
    L5_CLOSE_TAC;
    ARM_BSTEP_TAC L5_EXEC (4--5) THEN
    CF2_L5B_FIX_TAC `X4` `word(ip + x):int64` CF2_L5B_VAL_TAC THEN
    CF2_L5B_FIX_TAC `X6` `word(ip + x):int64` CF2_L5B_VAL_TAC THEN
    ARM_BSTEP_TAC L5_EXEC (6--7) THEN
    SUBGOAL_THEN
     `ival(word(ip + x):int64) = &(ip + x) /\
      ival(word 7:int64) = &7 /\
      ival(word_sub (word(ip + x)) (word 7):int64) = &(ip + x) - &7`
     STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC CF2_L5B_IVAL_WORD64) THEN
      TRY(MATCH_MP_TAC L5_IVAL_SUB64) THEN CONV_TAC NUM_REDUCE_CONV THEN
      CF2_ARITH_TAC;
      ALL_TAC] THEN
    W(fun (asl,w) -> CF2_L5B_BRANCH_TAC `ip + x <= 7`
       (CF2_L5B_SCOND_TAC (cf2_l5b_ival_facts asl))) THENL
     [L5_J13_TAC 8 `t2:num->num`;
      L5_GT7_TAC THEN L5_J13_TAC 22 L5_T2A_GT]]);;
