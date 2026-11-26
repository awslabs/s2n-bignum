(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing a message with a SHAKE256 pre-hash (HashML-DSA): the proof (see   *)
(* signature_pre_hash_shake256_65_spec.ml).                                  *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/signature_pre_hash_shake256_65_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_wrap.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sponge3.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_prehash.ml";;

(* ------------------------------------------------------------------------- *)
(* The inlined SHAKE256 of the message, as the region lemmas of              *)
(* inline_sponge2.ml and inline_sponge3.ml for this function: the loop over  *)
(* the blocks of 136 bytes, the XOR of the rest, the absorbing as a whole,   *)
(* and the padding with the last permutation.                                *)
(* ------------------------------------------------------------------------- *)

let MLD_SPHS65_FN = "mldsa65_signature_pre_hash_shake256";;
let MLD_SPHS65_EXEC =
  MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_65_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;
let MLD_SPHS65_TAIL = PROVE_SPONGE3_TAIL MLD_SPHS65_FN "X25" "X24";;
let MLD_SPHS65_L1 = PROVE_SPONGE2_L1 MLD_SPHS65_FN "X25" "X24";;
let MLD_SPHS65_ABS =
  PROVE_SPONGE3_ABS MLD_SPHS65_FN "X25" "X24" MLD_SPHS65_L1 MLD_SPHS65_TAIL;;
let MLD_SPHS65_FIN = PROVE_SPONGE2_FIN MLD_SPHS65_FN "X25" "X24";;

let MLD_SPHS65_VARS =
  [`sig:int64`; `m:int64`; `mlen:num`; `ctx:int64`; `ctxlen:num`; `rnd:int64`;
   `sk:int64`; `skb:num->byte`; `M:num`; `C:num`; `RND:num`; `PH:num`; `MU:num`;
   `guard:int64`; `mf:int64`; `mc:int64`; `pc:num`; `stackpointer:int64`;
   `returnaddress:int64`];;

let ASM_NZ_TAC ths = W(fun (asl,_) -> REWRITE_TAC(ths @ map snd (filter (fun (_,th) -> concl th <> `ctxlen = 0`) asl)));;

let sphs_sp_off sname =
  let pat = `read SP (s:armstate) = word_add stackpointer (word (k:num))` in
  let s = mk_var(sname,`:armstate`) in
  tryfind (fun (_,th) ->
    let c = concl th in
    if not(is_eq c && can (term_match [] pat) c) || rand(lhand c) <> s then failwith "no"
    else dest_small_numeral(rand(rand(rhs c)))) ;;

let SPHS_ADDR k =
  mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
          mk_comb(`word:num->int64`,mk_small_numeral k));;

(*** The 8 bytes of the state above the 192 that the stores of 32 bytes
     cover: bytes 256..263 from the store of 16 bytes at sp + 252 ***)

let SPHS_PIECE_TAC sname =
  let s = mk_var(sname,`:armstate`) in
  W(fun (asl,_) ->
    let k = sphs_sp_off sname asl in
    let a252 = SPHS_ADDR(k + 252) in
    MP_TAC(SPECL [a252; `word 0:int128`; s] READ_MEMORY_BYTES_OF_WORD128) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD_0] THEN DISCH_TAC THEN
    MP_TAC(SPECL [a252; `16`; `0`; `4`; `8`; s] SPONGE2_BYTES_SUB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[DIV_0; MOD_0] THEN
    CONV_TAC(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC DEPTH_CONV NUM_ADD_CONV) THEN
    DISCH_TAC);;

let SPHS_STATE_ZERO_TAC sname =
  let s = mk_var(sname,`:armstate`) in
  W(fun (asl,_) ->
    let k = sphs_sp_off sname asl in
    let a = SPHS_ADDR(k + 64) in
    MP_TAC(SPECL [a; s] SPONGE3_ZERO_STATE) THEN
    ANTS_TAC THENL
     [CONV_TAC(DEPTH_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC DEPTH_CONV NUM_ADD_CONV) THEN
      ASM_REWRITE_TAC[];
      DISCH_TAC]);;

let SPHS65_HEAD =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLD_SPHS65_EXEC (1--8) THEN
  MLD_WRAP_SYMBUF_TAC `kb:num` THEN MLD_WRAP_SYMBUF_END_TAC `kb:num` THEN
  ARM_STEPS_TAC MLD_SPHS65_EXEC (9--9) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_SPHS65_EXEC (10--22) THEN
  SPHS_PIECE_TAC "s22" THEN
  ARM_STEPS_TAC MLD_SPHS65_EXEC (23--28) THEN
  SPHS_STATE_ZERO_TAC "s28";;

(*** Arithmetic from the small facts on numbers among the assumptions: the
     comparisons and equations of numbers (type num) of size at most 60, which
     leaves out the many other assumptions that ASM_ARITH_TAC would parse ***)

let SPHS_ARITH_TAC =
  W(fun (asl,_) ->
    let ok th =
      let c = concl th in
      (is_eq c || (try fst(dest_const(rator(rator c))) = "<=" || fst(dest_const(rator(rator c))) = "<" with Failure _ -> false)) &&
      (try type_of(lhand c) = `:num` with Failure _ -> false) &&
      (try String.length(string_of_term c) < 120 with _ -> false) in
    MAP_EVERY MP_TAC (filter ok (map snd asl)) THEN ARITH_TAC);;

let SPHS_SPVAL_TAC n k nc =
  let tn = mk_small_numeral n and tk = mk_small_numeral k
  and tc = mk_small_numeral nc in
  SUBGOAL_THEN
   (subst [tc,`nc:num`; tk,`k:num`]
     `nc <= val(word_add stackpointer (word k):int64) /\
      val(word_add stackpointer (word k):int64) < 2 EXP 63`)
   ASSUME_TAC THENL
   [SUBGOAL_THEN
     (subst [tn,`n:num`] `n <= val(word_add stackpointer (word n):int64)`)
     ASSUME_TAC THENL [SPHS_ARITH_TAC; ALL_TAC] THEN
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
    STRIP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SPHS_ARITH_TAC;
    ALL_TAC];;

let SPHS_CALL_FACTS_TAC n nc =
  let pat = `read SP (s:armstate) = word_add stackpointer (word (k:num))` in
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if not(is_eq c && can (term_match [] pat) c) then failwith "no" else
    let k = dest_small_numeral(rand(rand(rhs c))) in
    SPHS_SPVAL_TAC n k 32768 THEN SPHS_SPVAL_TAC n (k - nc) 0);;

let SPHS_SPBOUND_TAC k =
  let tn = `15168` and tk = mk_small_numeral k in
  SUBGOAL_THEN
   (subst [tk,`k:num`] `val(word_add stackpointer (word k):int64) + 464 < 2 EXP 63`)
   ASSUME_TAC THENL
   [SUBGOAL_THEN `15168 <= val(word_add stackpointer (word 15168):int64)` ASSUME_TAC THENL [SPHS_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`stackpointer:int64`; tn; tk] MLD_CLANG_VAL_ADD) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
    MP_TAC(SPECL [`stackpointer:int64`; tn; tn] MLD_CLANG_VAL_ADD) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
    STRIP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SPHS_ARITH_TAC;
    ALL_TAC];;

let SPHS65_ABS_TAC =
  SUBGOAL_THEN `val(word mlen:int64) = mlen` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN SPHS_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word mlen:int64) = mlen`]) THEN
  W(fun (asl,_) ->
    let k = sphs_sp_off "s28" asl in
    SPHS_SPBOUND_TAC k THEN
    SPONGE2_SPEC_HYP "H_ABS" "H_ABS0"
     [`m:int64`; `mlen:num`; `M:num`; SPHS_ADDR k; `pc:num`]);;

let SPHS65_FIN_TAC =
  SUBGOAL_THEN `mlen MOD 136 < 136` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  W(fun (asl,_) ->
    let k = sphs_sp_off "s29" asl in
    SPONGE2_SPEC_HYP "H_FIN" "H_FIN0"
     [`FST(mld_keccak_absorb 136 (word 0) 0 mlen M)`; `mlen MOD 136`; SPHS_ADDR k; `pc:num`]) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc MLD_SPHS65_EXEC "H_FIN0" [] MLD_SPHS65_VARS 30;;

let SPHS_XSTATE = `keccak_f1600 (mld_keccak_finalize 136 31 (FST (mld_keccak_absorb 136 (word 0) 0 mlen M)) (mlen MOD 136))`;;


let SPHS_CHUNK_FACTS_TAC sname =
  let s = mk_var(sname,`:armstate`) in
  W(fun (asl,_) ->
    let k0 = sphs_sp_off sname asl in
    let a = SPHS_ADDR(k0 + 64) in
    FIRST_ASSUM(fun wth ->
      if concl wth <> mk_eq(mk_comb(mk_comb(`read:(armstate,1600 word)component->armstate->1600 word`,
            mk_comb(mk_comb(`(:>):(armstate,int64->byte)component->(int64->byte,1600 word)component->(armstate,1600 word)component`,`memory`),
                    mk_comb(`wbytes:int64->(int64->byte,1600 word)component`,a))),s),SPHS_XSTATE)
      then failwith "no" else
      MAP_EVERY (fun k ->
        let f = MP (SPECL [a; SPHS_XSTATE; mk_small_numeral k; s] SPONGE2_BYTES128_OF_WBYTES)
                   (CONJ wth (ARITH_RULE(mk_binop `(<):num->num->bool` (mk_small_numeral k) `12`))) in
        let f = CONV_RULE(DEPTH_CONV NUM_MULT_CONV) f in
        ASSUME_TAC f THEN ASSUME_TAC (SPONGE2_NORMADDR f)) (0--3)));;

let SPHS_PH_TAC sname =
  let s = mk_var(sname,`:armstate`) in
  W(fun (asl,_) ->
    let k = sphs_sp_off sname asl in
    let a0 = SPHS_ADDR k in
    SUBGOAL_THEN
     (mk_eq(mk_comb(mk_comb(`read:(armstate,num)component->armstate->num`,
              mk_comb(mk_comb(`(:>):(armstate,int64->byte)component->(int64->byte,num)component->(armstate,num)component`,`memory`),
                      mk_comb(`bytes:int64#num->(int64->byte,num)component`,mk_pair(a0,`64`)))),s),
            `num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64)`)) ASSUME_TAC THENL
     [REWRITE_TAC[SPONGE2_PH2] THEN
      MP_TAC(SPECL [a0; `4`; mk_comb(`val:1600 word->num`,SPHS_XSTATE); s] SPONGE2_BYTES_OF_BYTES128) THEN
      ANTS_TAC THENL
       [CONV_TAC(DEPTH_CONV EXPAND_CASES_CONV) THEN
        CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
        CONV_TAC(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC DEPTH_CONV NUM_ADD_CONV) THEN
        REPEAT CONJ_TAC THEN
        W(fun (_,w) -> FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = lhs w then (REWRITE_TAC[th] THEN REWRITE_TAC[word_subword] THEN CONV_TAC(DEPTH_CONV NUM_REDUCE_CONV) THEN NO_TAC) else NO_TAC));
        CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN DISCH_THEN ACCEPT_TAC];
      ALL_TAC]);;

let SPHS_LIBC_CALL_TAC name execth ilist vars n =
  REMOVE_THEN name (fun th ->
    LIBC_CONTRACT_SIM_TAC ~is_safety_thm:true execth th ilist n THENL
     [FULL_EXISTS_E2_TAC (ref vars); LABEL_TAC name th]);;

let SPHS65_MEMSET_TAC n =
  LIBC_PLT_TAC MLD_SPHS65_EXEC (n - 5) THEN
  SPHS_LIBC_CALL_TAC "H_MEMSET" MLD_SPHS65_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] MLD_SPHS65_VARS n THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_0]);;

let SPHS65_FINAL_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[MLD_WRAP_RET_DISTINCT] THEN
  REPEAT CONJ_TAC THEN TRY(MLD_WRAP_RET_TAC THEN NO_TAC) THEN
  ABBREV_TAC `rho = mld_sk_rho skb` THEN
  ABBREV_TAC `dcl = mld_sign_declass_65 skb MU RND` THEN
  MLD_WRAP_DISCHARGE_TAC;;

let SPHS65_R_TAC k =
  ARM_STEPS_TAC MLD_SPHS65_EXEC (k--(k + 17)) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_SPHS65_EXEC ((k + 18)--(k + 42)) THEN SPHS65_FINAL_TAC;;

let SPHS_ARITH_255 =
  FIRST_ASSUM(fun th -> if concl th = `ctxlen <= 255` then MP_TAC th else NO_TAC) THEN ARITH_TAC;;

let SPHS65_LEN_TAC =
  SUBGOAL_THEN `ctxlen <= 255` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM NOT_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `77 + ctxlen < 2 EXP 64` ASSUME_TAC THENL [SPHS_ARITH_255; ALL_TAC] THEN
  SUBGOAL_THEN `val(word ctxlen:int64) = ctxlen` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN SPHS_ARITH_255; ALL_TAC] THEN
  SUBGOAL_THEN `word_add (word ctxlen:int64) (word 77) = word(77 + ctxlen)` ASSUME_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC];;

let SPHS_OID_FACT sname =
  let s = mk_var(sname,`:armstate`) in
  MP_TAC(SPECL [s; `pc:num`] (MLDSA_NATIVE_IMAGE_CONST_RULE 248796 64)) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC];;

let SPHS_OID7_TAC sname a2 =
  let s = mk_var(sname,`:armstate`) in
  let x9 = `244603165765273862` in
  MP_TAC(SPECL [a2; mk_comb(`word:num->int64`,x9); s] READ_MEMORY_BYTES_OF_WORD64) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  MP_TAC(SPECL [a2; `8`; x9; `0`; `7`; s] SPONGE2_BYTES_SUB) THEN
  ANTS_TAC THENL [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ARITH_TAC]; ALL_TAC] THEN
  REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC;;

let SPHS65_MEMCPY_TAC n =
  LIBC_PLT_TAC MLD_SPHS65_EXEC (n - 5) THEN
  SPHS_LIBC_CALL_TAC "H_MEMCPY" MLD_SPHS65_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `C:num`; `read X30 s`]
   MLD_SPHS65_VARS n;;


let SPHS_XADDR k c =
  mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
    mk_comb(`word:num->int64`,
      mk_binop `(+):num->num->num` (mk_small_numeral k)
        (mk_binop `(+):num->num->num` `ctxlen:num` (mk_small_numeral c))));;



let SPHS_RD_BYTES2 s a n =
  mk_comb(mk_comb(`read:(armstate,num)component->armstate->num`,
     mk_comb(mk_comb(`(:>):(armstate,int64->byte)component->(int64->byte,num)component->(armstate,num)component`,`memory`),
             mk_comb(`bytes:int64#num->(int64->byte,num)component`,mk_pair(a,n)))), s);;

let SPHS_256_EXP = prove(`!n. 256 EXP n = 2 EXP (8 * n)`, GEN_TAC THEN REWRITE_TAC[EXP_MULT] THEN CONV_TAC NUM_REDUCE_CONV);;

let SPHS_RD_BYTES2 s a n =
  mk_comb(mk_comb(`read:(armstate,num)component->armstate->num`,
     mk_comb(mk_comb(`(:>):(armstate,int64->byte)component->(int64->byte,num)component->(armstate,num)component`,`memory`),
             mk_comb(`bytes:int64#num->(int64->byte,num)component`,mk_pair(a,n)))), s);;

(*** The facts on the bytes that the code stores: ctxlen as a byte ***)

let SPHS65_BYTE_FACTS =
  MP_TAC(SPEC `ctxlen:num` MLD_PREFIX_VAL_BYTE) THEN
  ANTS_TAC THENL [SPHS_ARITH_255; ALL_TAC] THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word 1:byte) = 1` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC];;

(*** The prefix in the buffer at sp + 64 after the stores at x8 = sp + 64 +
     ctxlen, as a number (state sn, stack pointer sp = stackpointer + k0) ***)

let SPHS_PREFIX_TAC sn k0 =
  let kk = k0 + 64 in
  let s = mk_var(sn,`:armstate`) in
  let a = SPHS_ADDR kk in
  let rd a n = SPHS_RD_BYTES2 s a n in
  let xa c = SPHS_XADDR kk c in
  let kt = mk_small_numeral kk in
  let arith str = ARITH_RULE(parse_term str) in
  let norm = CONV_TAC(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC DEPTH_CONV NUM_ADD_CONV) in
  let facts =
    (*** F1: the two bytes 1 and ctxlen ***)
    SUBGOAL_THEN (mk_eq(rd a `2`,`1 + 256 * ctxlen`)) ASSUME_TAC THENL
     [REWRITE_TAC[MLD_PREFIX_BYTES2] THEN norm THEN ASM_NZ_TAC[VAL_WORD_0] THEN
       TRY(FIRST_ASSUM(fun th -> if concl th = `ctxlen < 1` then MP_TAC th else NO_TAC)) THEN ARITH_TAC;
      ALL_TAC] THEN
    (*** F3: the 11 bytes of the OID ***)
    SUBGOAL_THEN (mk_eq(rd (xa 9) `4`,`201458691`)) ASSUME_TAC THENL
     [MP_TAC(SPECL [xa 9; `word 201458691:int32`; s] READ_MEMORY_BYTES_OF_WORD32) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN
     (mk_eq(rd (mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
                  mk_comb(`word:num->int64`,mk_binop `(+):num->num->num` kt `2 + ctxlen`)))
               `11`,`14516628599920749990381830`)) ASSUME_TAC THENL
     [REWRITE_TAC[arith(Printf.sprintf "%d + (2 + ctxlen) = %d + (ctxlen + 2)" kk kk)] THEN
      MP_TAC(SPECL [xa 2; `7`; `4`; s] MLD_PREFIX_BYTES_COMBINE) THEN
      REWRITE_TAC[ARITH_RULE `7 + 4 = 11`] THEN norm THEN
      REWRITE_TAC[arith(Printf.sprintf "(%d + (ctxlen + 2)) + 7 = %d + (ctxlen + 9)" kk kk)] THEN
      ASM_NZ_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN ACCEPT_TAC;
      ALL_TAC] THEN
    (*** F4: the 64 bytes of the pre-hash ***)
    SUBGOAL_THEN
     (mk_eq(rd (mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
                  mk_comb(`word:num->int64`,mk_binop `(+):num->num->num` kt `13 + ctxlen`)))
               `64`,`num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64)`)) ASSUME_TAC THENL
     [REWRITE_TAC[arith(Printf.sprintf "%d + (13 + ctxlen) = %d + (ctxlen + 13)" kk kk)] THEN
      REWRITE_TAC[SPONGE2_PH2] THEN
      MP_TAC(SPECL [xa 13; `4`; mk_comb(`val:1600 word->num`,SPHS_XSTATE); s] SPONGE2_BYTES_OF_BYTES128) THEN
      ANTS_TAC THENL
       [CONV_TAC(DEPTH_CONV EXPAND_CASES_CONV) THEN
        CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN norm THEN
        REWRITE_TAC(map arith
          [Printf.sprintf "(%d + (ctxlen + 13)) + 16 = %d + (ctxlen + 29)" kk kk;
           Printf.sprintf "(%d + (ctxlen + 13)) + 32 = %d + (ctxlen + 45)" kk kk;
           Printf.sprintf "(%d + (ctxlen + 13)) + 48 = %d + (ctxlen + 61)" kk kk;
           Printf.sprintf "(%d + (ctxlen + 13)) + 0 = %d + (ctxlen + 13)" kk kk]) THEN
        REPEAT CONJ_TAC THEN
        W(fun (_,w) -> FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = lhs w then (REWRITE_TAC[th] THEN REWRITE_TAC[word_subword] THEN CONV_TAC(DEPTH_CONV NUM_REDUCE_CONV) THEN NO_TAC) else NO_TAC));
        CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN DISCH_THEN ACCEPT_TAC];
      ALL_TAC] in
  facts THEN
  (*** the number of the prefix ***)
  SUBGOAL_THEN `C < 256 EXP ctxlen` ASSUME_TAC THENL
   [REWRITE_TAC[SPHS_256_EXP] THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [`ctx:int64`;`ctxlen:num`;`C:num`] `read (memory :> bytes(ctx,ctxlen)) (t:armstate) = C`) (concl th)
      then ACCEPT_TAC(MATCH_MP MLD_WRAP_READ_BYTES_BOUND th) else NO_TAC);
    ALL_TAC] THEN
  SUBGOAL_THEN `num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64) < 256 EXP 64` ASSUME_TAC THENL
   [REWRITE_TAC[SPHS_256_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [`mlen:num`;`M:num`] `read (memory :> bytes(a:int64,64)) (t:armstate) = num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64)`) (concl th)
      then ACCEPT_TAC(CONV_RULE(RAND_CONV NUM_REDUCE_CONV)(MATCH_MP MLD_WRAP_READ_BYTES_BOUND th)) else NO_TAC);
    ALL_TAC] THEN
  MP_TAC(SPECL [a; `ctxlen:num`; `C:num`;
                `num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64)`; s]
               MLD_SPHS_PREFIX_MEM) THEN
  ANTS_TAC THENL
   [norm THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`ctxlen:num`; `C:num`;
                `num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64)`]
               MLD_SPHS_PREFIX_NUM) THEN
  ANTS_TAC THENL [ASM_NZ_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun pn ->
    ASSUME_TAC pn THEN
    SUBGOAL_THEN
     (mk_eq(rd a `77 + ctxlen`,
        `num_of_bytelist(mld_domain_separation_prefix 12 (bytelist_of_num ctxlen C)
           (bytelist_of_num 64 (num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64))))`))
     ASSUME_TAC THENL
     [REWRITE_TAC[pn; ARITH_RULE `77 + ctxlen = ctxlen + 77`] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC]);;

(*** The calls: the facts on the stack pointer of the callee, the regions that
     do not overlap the buffer of plen <= 332 bytes at sp + 64 (by the bound
     bth: plen <= 332), and the widening of the region of the buffer in the
     events after the call, as MLD_CLANG_DRIVER_TAC and MLD_CLANG_WIDEN_TAC
     do for a buffer at sp ***)

let SPHS65_DRIVER_TAC nc regs bth =
  let pat = `read SP (s:armstate) = word_add stackpointer (word (k:num))` in
  let plen = lhand(concl bth) in
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if not(is_eq c && can (term_match [] pat) c) then failwith "no" else
    let k = dest_small_numeral(rand(rand(rhs c))) in
    let stk = mk_pair(SPHS_ADDR (k - nc),mk_small_numeral nc)
    and buf = mk_pair(SPHS_ADDR (k + 64),plen) in
    MAP_EVERY (fun r -> MLD_WRAP_DRIVER_TAC
      (mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,r),buf)) bth)
     (stk :: regs));;


let SPHS65_WIDEN_TAC bth =
  let pat = `read SP (s:armstate) = word_add stackpointer (word (k:num))` in
  let plen = lhand(concl bth) in
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if not(is_eq c && can (term_match [] pat) c) then failwith "no" else
    let k = dest_small_numeral(rand(rand(rhs c))) in
    let a = SPHS_ADDR (k + 64) in
    let ct = mk_comb(mk_comb(`contained:int64#num->int64#num->bool`,
                             mk_pair(a,plen)),mk_pair(a,`332`)) in
    let cth = MP (prove(mk_imp(concl bth,ct),
                        REWRITE_TAC[contained; CONTAINED_MODULO_REFL; DIMINDEX_64] THEN
                        CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[])) bth in
    MLD_WRAP_WIDEN_TAC [cth]);;

(*** The case ctxlen = 0 is remembered as ctxlen < 1 after the branch on it,
     so that the simulation of the stores with the offset ctxlen keeps the
     addresses as sums with ctxlen, as for ctxlen <> 0; the case fact is put
     back after the call ***)

(*** The fact val(word ctxlen) = ctxlen would turn the test of the code on the
     value of ctxlen into an equation ctxlen = 0, which the simulation then
     uses to replace ctxlen by 0 in the goal; so it is dropped when the
     branch is simulated, with the case fact val(word ctxlen) = 0 or not ***)

let SPHS_DROP_VAL_TAC =
  FIRST_X_ASSUM(fun th ->
    if concl th = `val(word ctxlen:int64) = ctxlen` then ALL_TAC else NO_TAC);;

let SPHS_FORGET_ZERO_TAC =
  FIRST_X_ASSUM(fun th ->
    if concl th = `ctxlen = 0`
    then ASSUME_TAC(MP (ARITH_RULE `ctxlen = 0 ==> ctxlen < 1`) th) else NO_TAC);;

let SPHS_RESTORE_ZERO_TAC = ALL_TAC;;

let SPHS65_Z_TAC k =
  ARM_STEPS_TAC MLD_SPHS65_EXEC (k--(k + 3)) THEN
  SPHS65_MEMSET_TAC (k + 8) THEN SPHS65_R_TAC (k + 9);;

(*** The call of the internal function, from the stores of the prefix at the
     state of the last store (step b + 23), and what follows: the zeroing,
     by cases on whether signing succeeds ***)

let SPHS65_SIGN_TAC b =
  let sn = "s" ^ string_of_int (b + 23) in
  W(fun (asl,_) ->
    let k0 = sphs_sp_off sn asl in
    SPHS_PREFIX_TAC sn k0 THEN
    SUBGOAL_THEN `77 + ctxlen <= 332` ASSUME_TAC THENL [SPHS_ARITH_255; ALL_TAC] THEN
    MLD_WRAP_GOT_TAC THEN
    MLD_WRAP_NULL_TAC [`sig:int64`,`3309`; `stackpointer:int64`,`15168`] THEN
    MLD_WRAP_MP_TAC `ctxlen <= 255` THEN
    ASSUME_TAC(INST_TYPE [`:64`,`:M`; `:32`,`:N`] WORD_ZX_0) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MLD_WRAP_PREFIX_LENGTH_SHAKE256]) THEN
    MLD_WRAP_USE_CASE_TAC `255 < ctxlen` [ADD_EQ_0; ARITH_EQ] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `ctxlen + 77 = 77 + ctxlen`]) THEN
    SPHS_CALL_FACTS_TAC 15168 14624 THEN
    SPHS65_DRIVER_TAC 14624 [`sig:int64,3309`] (ASSUME `77 + ctxlen <= 332`) THEN
    ARM_STEPS_TAC MLD_SPHS65_EXEC ((b + 24)--(b + 24)) THEN
    FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc MLD_SPHS65_EXEC
     "H_INTERNAL"
     [`read X0 s`; `read X1 s`; `77 + ctxlen`; `read X3 s`; `0`;
      `read X5 s`; `read X6 s`; `read X7 s`; `skb:num->byte`;
      `num_of_bytelist(mld_domain_separation_prefix 12 (bytelist_of_num ctxlen C)
         (bytelist_of_num 64 (num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64))))`;
      `0`; `RND:num`; `MU:num`; `guard:int64`; `pc:num`; `read SP s`; `read X30 s`]
     MLD_SPHS65_VARS (b + 25) THEN
    SPHS65_WIDEN_TAC (ASSUME `77 + ctxlen <= 332`) THEN
    SPHS_RESTORE_ZERO_TAC THEN
    ASM_CASES_TAC `mld_sign_ok_65 skb MU RND` THEN
    MLD_WRAP_USE_CASE_TAC `mld_sign_ok_65 skb MU RND` [] THEN
    FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[MLD_WRAP_SIGN_OK_DECLASS_65] o
      check (fun th -> concl th = `mld_sign_ok_65 skb MU RND` ||
                       concl th = `~mld_sign_ok_65 skb MU RND`)) THEN
    MLD_CLANG_IF `mld_sign_ok_65 skb MU RND`
     (ARM_STEPS_TAC MLD_SPHS65_EXEC ((b + 26)--(b + 27)) THEN SPHS65_R_TAC (b + 28))
     (ASSUME_TAC(GEN `t:num` (MP (SPECL [`skb:num->byte`; `MU:num`;
        `RND:num`; `t:num`] (CONJUNCT1(CONJUNCT2 MLD_WRAP_SIGN_SIG_FAIL)))
        (ASSUME `~mld_sign_ok_65 skb MU RND`))) THEN
      ARM_STEPS_TAC MLD_SPHS65_EXEC ((b + 26)--(b + 27)) THEN
      SPHS65_Z_TAC (b + 28)));;



(*** The prefix is built at x8 = sp + 64 + ctxlen by stores after the
     context is in the buffer (steps b + 1 to b + 23 from the state of step
     b, at 0x220), then the call of the internal function ***)

let SPHS65_BUILD_TAC b =
  let st n = "s" ^ string_of_int n in
  ARM_STEPS_TAC MLD_SPHS65_EXEC ((b + 1)--(b + 4)) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_SPHS65_EXEC ((b + 5)--(b + 5)) THEN
  SPHS_OID_FACT (st (b + 5)) THEN
  ARM_STEPS_TAC MLD_SPHS65_EXEC ((b + 6)--(b + 20)) THEN
  W(fun (asl,_) ->
    let k0 = sphs_sp_off (st (b + 20)) asl in
    SPHS_OID7_TAC (st (b + 20)) (SPHS_XADDR (k0 + 64) 2)) THEN
  ARM_STEPS_TAC MLD_SPHS65_EXEC ((b + 21)--(b + 23)) THEN
  SPHS65_SIGN_TAC b;;

let SPHS65_SETUP =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mcp = CONJ_PAIR th in
    MLD_WRAP_ASSUME_CALLEE_TAC
     (MATCH_MP MLDSA_NATIVE_SIGNATURE_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
               (CONJ ms mcp)) "H_INTERNAL" THEN
    MLD_WRAP_ASSUME_CALLEE_TAC (REWRITE_RULE[memcpy_full_contract] mcp) "H_MEMCPY" THEN
    MLD_WRAP_ASSUME_CALLEE_TAC (REWRITE_RULE[memset_full_contract] ms) "H_MEMSET" THEN
    MLD_WRAP_ASSUME_CALLEE_TAC MLD_SPHS65_ABS "H_ABS" THEN
    MLD_WRAP_ASSUME_CALLEE_TAC MLD_SPHS65_FIN "H_FIN") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(sig:int64) (m:int64) (mlen:num) (ctx:int64) (ctxlen:num) (rnd:int64)
     (sk:int64) (rho:num)
     (dcl:num->num#num#(num->int32)#(num->byte)) (guard:int64) (mf:int64)
     (mc:int64) (pc:num) (sp:int64) (ra:int64).
     if aligned 32 sp then
       if 255 < ctxlen
       then f_ev_a0 sig m mlen ctx ctxlen rnd sk guard mf mc pc sp ra
       else if ctxlen < 1
       then (if (?n. FST(SND(dcl n)) = 18)
             then f_ev_a1 sig m mlen ctx ctxlen rnd sk rho dcl guard mf mc pc sp ra
             else f_ev_a2 sig m mlen ctx ctxlen rnd sk rho dcl guard mf mc pc sp ra)
       else (if (?n. FST(SND(dcl n)) = 18)
             then f_ev_a3 sig m mlen ctx ctxlen rnd sk rho dcl guard mf mc pc sp ra
             else f_ev_a4 sig m mlen ctx ctxlen rnd sk rho dcl guard mf mc pc sp ra)
     else
       if 255 < ctxlen
       then f_ev_u0 sig m mlen ctx ctxlen rnd sk guard mf mc pc sp ra
       else if ctxlen < 1
       then (if (?n. FST(SND(dcl n)) = 18)
             then f_ev_u1 sig m mlen ctx ctxlen rnd sk rho dcl guard mf mc pc sp ra
             else f_ev_u2 sig m mlen ctx ctxlen rnd sk rho dcl guard mf mc pc sp ra)
       else (if (?n. FST(SND(dcl n)) = 18)
             then f_ev_u3 sig m mlen ctx ctxlen rnd sk rho dcl guard mf mc pc sp ra
             else f_ev_u4 sig m mlen ctx ctxlen rnd sk rho dcl guard mf mc pc sp ra)
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `m:int64`; `mlen:num`; `ctx:int64`;
    `ctxlen:num`; `rnd:int64`; `sk:int64`; `skb:num->byte`; `M:num`; `C:num`;
    `RND:num`; `PH:num`; mk_var("PRE",`:num`); `MU:num`; `guard:int64`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 15168 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLD_SPHS65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = v)))
   [`PH:num`; mk_var("PRE",`:num`)] THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `MU:num`)) THEN
  MLD_WRAP_FRAME_TAC 15168
   [`got_stack_chk_guard:num`; `got_memset:num`; `got_memcpy:num`]
   ((19--25) @ [28; 29]);;



(*** ctxlen > 255: the signature is zeroed and the result is -9 ***)

let SPHS65_REJECT_TAC =
  ARM_STEPS_TAC MLD_SPHS65_EXEC (44--50) THEN SPHS65_MEMSET_TAC 55 THEN SPHS65_R_TAC 56;;

(*** ctxlen = 0: no copy of the context ***)

let SPHS65_EMPTY_PRE =
  SUBGOAL_THEN `val(word ctxlen:int64) = 0` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if concl th = `val(word ctxlen:int64) = ctxlen` then MP_TAC th else NO_TAC) THEN
    FIRST_ASSUM(fun th -> if concl th = `ctxlen < 1` then MP_TAC th else NO_TAC) THEN ARITH_TAC;
    ALL_TAC] THEN
  SPHS_DROP_VAL_TAC THEN
  ARM_STEPS_TAC MLD_SPHS65_EXEC (44--48) THEN
  W(fun (asl,_) ->
    let k0 = sphs_sp_off "s48" asl in
    SUBGOAL_THEN
     (mk_eq(SPHS_RD_BYTES2 `s48:armstate` (SPHS_ADDR (k0 + 66)) `ctxlen:num`,`C:num`))
     ASSUME_TAC THENL
     [SUBGOAL_THEN `ctxlen = 0` ASSUME_TAC THENL
       [FIRST_ASSUM(fun th -> if concl th = `ctxlen < 1` then MP_TAC th else NO_TAC) THEN ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `C = 0` ASSUME_TAC THENL
       [FIRST_ASSUM(fun th ->
          if can (term_match [`ctx:int64`;`ctxlen:num`;`C:num`] `read (memory :> bytes(ctx,ctxlen)) (t:armstate) = C`) (concl th)
          then MP_TAC(MATCH_MP MLD_WRAP_READ_BYTES_BOUND th) else NO_TAC) THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL];
      ALL_TAC]);;

let SPHS65_EMPTY_TAC =
  SPHS65_EMPTY_PRE THEN
  SPHS65_BUILD_TAC 48;;

(*** ctxlen <> 0: the context is copied by memcpy into the buffer ***)

let SPHS65_COPY_TAC =
  SUBGOAL_THEN `~(val(word ctxlen:int64) = 0)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if concl th = `val(word ctxlen:int64) = ctxlen` then MP_TAC th else NO_TAC) THEN
    FIRST_ASSUM(fun th -> if concl th = `~(ctxlen < 1)` then MP_TAC th else NO_TAC) THEN ARITH_TAC;
    ALL_TAC] THEN
  SPHS_DROP_VAL_TAC THEN
  ARM_STEPS_TAC MLD_SPHS65_EXEC (44--52) THEN
  FIRST_X_ASSUM(fun th -> if concl th = `~(val(word ctxlen:int64) = 0)` then ALL_TAC else NO_TAC) THEN
  SUBGOAL_THEN `val(word ctxlen:int64) = ctxlen` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN SPHS_ARITH_255; ALL_TAC] THEN
  MLD_CLANG_OR_OFS_TAC 64 THEN
  ARM_STEPS_TAC MLD_SPHS65_EXEC (53--53) THEN SPHS65_MEMCPY_TAC 58 THEN
  SPHS65_BUILD_TAC 58;;

let SPHS65_OK_TAC =
  SPHS65_LEN_TAC THEN SPHS65_BYTE_FACTS THEN ASM_CASES_TAC `ctxlen < 1` THEN
  MLD_CLANG_IF `ctxlen < 1` SPHS65_EMPTY_TAC SPHS65_COPY_TAC;;

let SPHS65_FULL_TAC =
  SPHS65_SETUP THEN SPHS65_HEAD THEN SPHS65_ABS_TAC THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc MLD_SPHS65_EXEC "H_ABS0" [] MLD_SPHS65_VARS 29 THEN
  SPHS65_FIN_TAC THEN SPHS_CHUNK_FACTS_TAC "s30" THEN
  ARM_STEPS_TAC MLD_SPHS65_EXEC (31--43) THEN SPHS_PH_TAC "s43" THEN
  MLD_CLANG_CTX_TAC THEN ASM_CASES_TAC `255 < ctxlen` THEN
  MLD_WRAP_USE_CASE_TAC `255 < ctxlen` [ADD_EQ_0; ARITH_EQ] THEN
  ASSUME_TAC(ARITH_RULE `255 <= ctxlen /\ ~(ctxlen = 255) <=> 255 < ctxlen`) THEN
  MLD_CLANG_IF `255 < ctxlen` SPHS65_REJECT_TAC SPHS65_OK_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, by cases on whether the     *)
(* context is too long, empty or not, and whether signing succeeds, and, from *)
(* the prologue on, on whether the stack pointer is a multiple of 32.        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  SPHS65_FULL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  MLD_WRAP_CORRECT_TAC
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  MLD_WRAP_SAFE_TAC
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;
