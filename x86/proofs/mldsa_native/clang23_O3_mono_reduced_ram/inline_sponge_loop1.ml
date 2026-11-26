(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The loop over the full blocks of 136 bytes of the SHAKE256 that clang 23  *)
(* inlines into mldsa{44,65,87}_signature_pre_hash_shake256 and _verify_...  *)
(* (the loop labelled loop1 there): each iteration XORs the next 136 bytes   *)
(* of the message at R12 into the state of 200 bytes at rsp0 + 32, with 8    *)
(* pairs of MOVUPS/XORPS/MOVAPS and a 64-bit XOR, and calls                  *)
(* mldsa_keccakf1600_permute. The lemma goes from the head of the loop, for  *)
(* a message of mlen >= 136 bytes, to its exit (join1), where the state is   *)
(* that of mld_keccak_absorb_blocks after the n = mlen DIV 136 blocks and    *)
(* R12 and R13 are the rest of the message and its length. The scratch       *)
(* register that holds the address of the state is R14 in the signing        *)
(* function and RBX in the verification function, as the argument sr.        *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sponge_b.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/keccakf1600_permute_spec.ml";;
needs "x86/proofs/utils/mldsa_native_memset.ml";;
needs "x86/proofs/utils/mldsa_native_full.ml";;
needs "x86/proofs/utils/mldsa_native_signing.ml";;
needs "common/mldsa_native_fips202.ml";;

let SPONGE_L1_EXEC fn = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [(layout (fn^"_loop1"), layout (fn^"_loop1_exit"))];;

let SPONGE_L1_STMT fn sr = parse_term(Printf.sprintf
 "exists f_events. forall e m mlen M rsp0 n (S0:1600 word) pc.
   aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   aligned 16 rsp0 /\\ mlen DIV 136 = n /\\ 0 < n /\\ mlen < 2 EXP 64 /\\
   nonoverlapping (m,mlen) (word_sub rsp0 (word 296),528) /\\
   nonoverlapping (word pc,libmldsa_size) (word_sub rsp0 (word 296),528)
   ==> ensures x86
    (\\s. bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
          read RIP s = word (pc + %s_loop1) /\\ read RSP s = rsp0 /\\
          read R12 s = m /\\ read R13 s = word mlen /\\
          read %s s = word_add rsp0 (word 32) /\\
          read (memory :> bytes(m,mlen)) s = M /\\
          read (memory :> wbytes (word_add rsp0 (word 32))) s = S0 /\\
          read events s = e)
    (\\s. read RIP s = word (pc + %s_loop1_exit) /\\ read RSP s = rsp0 /\\
          read R12 s = word_add m (word (136 * n)) /\\
          read R13 s = word (mlen - 136 * n) /\\
          read %s s = word_add rsp0 (word 32) /\\
          read (memory :> bytes(m,mlen)) s = M /\\
          read (memory :> wbytes (word_add rsp0 (word 32))) s =
            mld_keccak_absorb_blocks 136 S0 M n /\\
          (exists e2. read events s = APPEND e2 e /\\
             e2 = f_events m mlen rsp0 n pc /\\
             memaccess_inbounds e2
              [m,mlen; word_add rsp0 (word 32),200;
               word_sub (word_sub rsp0 (word 8)) (word 288),288;
               word_sub rsp0 (word 8),8;
               word(pc + rodata_mld_KeccakF_RoundConstants),192]
              [word_add rsp0 (word 32),200;
               word_sub (word_sub rsp0 (word 8)) (word 288),288;
               word_sub rsp0 (word 8),8]))
    (MAYCHANGE [RIP; RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [R12; R13] ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bytes(word_add rsp0 (word 32),200);
                memory :> bytes(word_sub (word_sub rsp0 (word 8)) (word 288),288);
                memory :> bytes(word_sub rsp0 (word 8),8)])"
  fn sr fn sr);;

let SPONGE_L1_INV sr = parse_term(Printf.sprintf
 "\\k s. read RSP s = rsp0 /\\
        read R12 s = word_add m (word (136 * k)) /\\
        read R13 s = word (mlen - 136 * k) /\\
        read %s s = word_add rsp0 (word 32) /\\
        read (memory :> bytes(m,mlen)) s = M /\\
        read (memory :> wbytes (word_add rsp0 (word 32))) s =
          mld_keccak_absorb_blocks 136 S0 M k" sr);;

(* The facts about numbers that the simulator needs as read facts *)

let SPONGE_WORD_MULT_CONV tm =
  match tm with
    Comb(Const("word",_),n) when is_binary "*" n && is_numeral(lhand n) && is_numeral(rand n) ->
      RAND_CONV NUM_MULT_CONV tm
  | _ -> failwith "SPONGE_WORD_MULT_CONV";;
let SPONGE_NUMRED = CONV_RULE(DEPTH_CONV SPONGE_WORD_MULT_CONV);;
let SPONGE_NORMADDR = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC DEPTH_CONV NUM_ADD_CONV);;
let SPONGE_A16 k = prove(mk_comb(mk_comb(`aligned:num->int64->bool`,`16`),mk_comb(`word:num->int64`,mk_small_numeral k)), REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUM_DIVIDES_CONV);;
let sponge_ltc t n = mk_binop `(<):num->num->bool` (mk_small_numeral t) (mk_small_numeral n);;

(*** The chunks of the 136 bytes of the block as subwords of word BLK ***)

let SPONGE_MSG_FACTS th0 bnd =
  let one lem nb t =
    let le = ARITH_RULE(mk_binop `(<=):num->num->bool`
             (mk_binop `(+):num->num->num` (mk_binop `(*):num->num->num` (mk_small_numeral nb) (mk_small_numeral t)) (mk_small_numeral nb)) `136`) in
    SPONGE_NUMRED(MATCH_MP lem (CONJ th0 le)) in
  MAP_EVERY (fun t -> let f = one READ_MEMORY_BYTES128_OF_NUM 16 t in
     let f' = REWRITE_RULE[MATCH_MP SPONGE_NUM_SUBWORD128 bnd] f in
     ASSUME_TAC f' THEN ASSUME_TAC (SPONGE_NORMADDR f')) [0;1;2;3;4;5;6;7] THEN
  (let f = one READ_MEMORY_BYTES64_OF_NUM 8 16 in
   let f' = REWRITE_RULE[MATCH_MP SPONGE_NUM_SUBWORD64 bnd] f in
   ASSUME_TAC f' THEN ASSUME_TAC (SPONGE_NORMADDR f'));;

(*** The chunks of the state as subwords of the state word ***)

let SPONGE_STATE_FACTS wth =
  MAP_EVERY (fun t -> let f = SPONGE_NUMRED(MATCH_MP READ_MEMORY_BYTES128_OF_WBYTES (CONJ wth (ARITH_RULE(sponge_ltc t 12)))) in
             ASSUME_TAC f THEN ASSUME_TAC (SPONGE_NORMADDR f)) [0;1;2;3;4;5;6;7] THEN
  MAP_EVERY (fun t -> let f = SPONGE_NUMRED(MATCH_MP READ_MEMORY_BYTES64_OF_WBYTES (CONJ wth (ARITH_RULE(sponge_ltc t 25)))) in
             ASSUME_TAC f THEN ASSUME_TAC (SPONGE_NORMADDR f)) [16;17;18;19;20;21;22;23;24];;

let SPONGE_ALIGN_FACTS = FIRST_ASSUM(fun ra -> if concl ra = `aligned 16 (rsp0:int64)` then
   MAP_EVERY (fun k -> ASSUME_TAC (MATCH_MP ALIGNED_WORD_ADD (CONJ ra (SPONGE_A16 k)))) [32;48;64;80;96;112;128;144;160]
   else NO_TAC);;

(*** The lanes of the stored chunks, and the high lanes of the block ***)

let SPONGE_LANE_FACTS sn =
  W(fun (asl,w) ->
    MAP_EVERY (fun (_,th) ->
      let c = concl th in
      if (match c with Comb(Comb(Const("=",_),l),_) -> (try let (_,n) = dest_comb l in n = mk_var(sn,`:x86state`) && can (term_match [] `read (memory :> bytes128 a) s`) l && free_in `rsp0:int64` l with Failure _ -> false) | _ -> false)
      then (let f = MATCH_MP READ_MEMORY_BYTES64_OF_BYTES128 th in
            let f1 = SPONGE_NUMRED(CONJUNCT1 f) and f2 = SPONGE_NUMRED(CONJUNCT2 f) in
            ASSUME_TAC (SPONGE_NORMADDR f1) THEN ASSUME_TAC (SPONGE_NORMADDR f2))
      else ALL_TAC) asl);;

let SPONGE_HI_FACTS = FIRST_ASSUM(fun th -> if concl th = `BLK < 2 EXP 1088` then
    MAP_EVERY (fun k -> ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_RED_CONV)(MATCH_MP SPONGE_SUBWORD_HI (CONJ th (ARITH_RULE(mk_binop `(<=):num->num->bool` `17` (mk_small_numeral k))))))) [17;18;19;20;21;22;23;24]
    else NO_TAC);;

let SPONGE_L1_VARS = [`m:int64`; `mlen:num`; `rsp0:int64`; `n:num`; `pc:num`; `i:num`];;

(*** The body of an iteration, from the invariant at the loop head ***)

let SPONGE_L1_BODY fn =
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    SUBGOAL_THEN `136 * (i + 1) <= mlen` ASSUME_TAC THENL
     [SUBGOAL_THEN `i + 1 <= n` MP_TAC THENL [UNDISCH_TAC `i < n` THEN ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `mlen DIV 136 = n` THEN
      MP_TAC(SPECL [`mlen:num`; `136`] DIVISION) THEN
      REPEAT(POP_ASSUM(K ALL_TAC)) THEN ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `BLK = (M DIV 2 EXP (8 * 136 * i)) MOD 2 EXP (8 * 136)` THEN
    ABBREV_TAC `XX = mld_keccak_absorb_blocks 136 S0 M i` THEN
    SUBGOAL_THEN `BLK < 2 EXP 1088` ASSUME_TAC THENL
     [EXPAND_TAC "BLK" THEN REWRITE_TAC[ARITH_RULE `8 * 136 = 1088`; MOD_LT_EQ_LT] THEN
      REWRITE_TAC[ARITH_RULE `0 < 2 EXP 1088`]; ALL_TAC] THEN
    SUBGOAL_THEN `BLK < 2 EXP 1600` ASSUME_TAC THENL
     [TRANS_TAC LTE_TRANS `2 EXP 1088` THEN ASM_REWRITE_TAC[LE_EXP] THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes(word_add m (word (136 * i)),136)) s0 = BLK` ASSUME_TAC THENL
     [EXPAND_TAC "BLK" THEN REWRITE_TAC[ARITH_RULE `8 * 136 * i = 8 * (136 * i)`] THEN
      MATCH_MP_TAC READ_MEMORY_BYTES_SUB THEN EXISTS_TAC `mlen:num` THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `136 * (i + 1) <= mlen` THEN ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes(word_add m (word (136 * i)),136)) s0 = BLK`) (concl th)
                          then SPONGE_MSG_FACTS th (ASSUME `BLK < 2 EXP 1600`) else NO_TAC) THEN
    FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> wbytes a) s0 = XX`) (concl th) && is_var(rand(concl th))
                          then SPONGE_STATE_FACTS th else NO_TAC) THEN
    SPONGE_ALIGN_FACTS THEN
    YMM_GHOST_TAC `s0:x86state` ["YMM0","y0"; "YMM1","y1"] THEN
    X86_STEPS_TAC (SPONGE_L1_EXEC fn) (1--30) THEN
    SPONGE_LANE_FACTS "s30" THEN SPONGE_HI_FACTS THEN
    SUBGOAL_THEN `read (memory :> wbytes (word_add rsp0 (word 32))) s30 = word_xor XX (word BLK:1600 word)` ASSUME_TAC THENL
     [MATCH_MP_TAC READ_MEMORY_WBYTES_OF_LANES THEN
      CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
      REPEAT CONJ_TAC THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      ASM_REWRITE_TAC[WORD_SUBWORD_XOR] THEN
      TRY(CONV_TAC WORD_BLAST THEN NO_TAC) THEN
      TRY(CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[WORD_XOR_0] THEN NO_TAC);
      ALL_TAC] THEN
    FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc (SPONGE_L1_EXEC fn) "H_PERMUTE"
      [`read RDI s`; `word_xor XX (word BLK:1600 word)`; `pc:num`; `read RSP s`;
       `read (memory :> bytes64 (read RSP s)) s`] SPONGE_L1_VARS 31 THEN
    X86_STEPS_TAC (SPONGE_L1_EXEC fn) (32--33) THEN
    SUBGOAL_THEN `i + 1 <= n` ASSUME_TAC THENL [UNDISCH_TAC `i < n` THEN ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> if concl th = `mlen < 2 EXP 64` then
      MP_TAC(MATCH_MP SPONGE_LOOP_JA (CONJ th (CONJ (ASSUME `mlen DIV 136 = n`) (ASSUME `i + 1 <= n`))))
      else NO_TAC) THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(fun a -> if can (term_match [] `read RIP s33 = x`) (concl a) || can (term_match [] `read events s33 = x`) (concl a) then REWRITE_RULE[th] a else a)) THEN
    FIRST_ASSUM(fun th -> if concl th = `mlen < 2 EXP 64` then
      MP_TAC(MATCH_MP SPONGE_LOOP_R13 (CONJ th (ASSUME `136 * (i + 1) <= mlen`)))
      else NO_TAC) THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(fun a -> if can (term_match [] `read R13 s33 = x`) (concl a) then REWRITE_RULE[th] a else a)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    FIRST
     [UNDISCH_TAC `0 < n` THEN ARITH_TAC;
      COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC;
      CONV_TAC WORD_RULE THEN NO_TAC;
      REWRITE_TAC[ARITH_RULE `136 * (i + 1) = 136 * i + 136`] THEN
      CONV_TAC WORD_RULE THEN NO_TAC;
      REWRITE_TAC[ARITH_RULE `i + 1 = SUC i`; mld_keccak_absorb_blocks] THEN
      MAP_EVERY (fun c -> FIRST_ASSUM(fun th -> if concl th = c then SUBST1_TAC(SYM th) else NO_TAC))
       [`mld_keccak_absorb_blocks 136 S0 M i = XX`;
        `(M DIV 2 EXP (8 * 136 * i)) MOD 2 EXP (8 * 136) = BLK`] THEN
      REWRITE_TAC[] THEN NO_TAC;
      SIGN_LOOP_DISCHARGE_TAC];;

(* The events of the callee are named ec, not e2 as in the postcondition of
   the loop, so that the two do not become one variable when they are chosen *)

let SPONGE_RENAME_E2 = CONV_RULE(DEPTH_CONV(fun tm ->
  if is_exists tm && name_of(fst(dest_exists tm)) = "e2"
  then ALPHA_CONV (mk_var("ec",type_of(fst(dest_exists tm)))) tm
  else failwith "SPONGE_RENAME_E2"));;

let SPONGE_L1_TAC fn sr =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   (SPONGE_RENAME_E2
    MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600)
   "H_PERMUTE" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(m:int64) (mlen:num) (rsp0:int64) (n:num) (pc:num).
      APPEND (f_ev_epil m mlen rsp0 n pc)
       (APPEND (ENUMERATEL n (\i. f_ev_loop m mlen rsp0 n pc i)) (f_ev_prol m mlen rsp0 n pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `m:int64`; `mlen:num`; `M:num`; `rsp0:int64`; `n:num`; `S0:1600 word`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; NONOVERLAPPING_CLAUSES; ALL; fst (SPONGE_L1_EXEC fn)] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `n:num` (parse_term (Printf.sprintf "pc + %s_loop1" fn))
   (parse_term (Printf.sprintf "pc + %s_loop1_exit" fn)) (SPONGE_L1_INV sr) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `0 < n` THEN ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[mld_keccak_absorb_blocks; MULT_CLAUSES; WORD_ADD_0; SUB_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    SPONGE_L1_BODY fn;
    FULL_EXIT0_TAC];;

(* ------------------------------------------------------------------------- *)
(* The lemma for each of the six functions that contain the loop: fn is the  *)
(* name of the function, and the register that holds the address of the      *)
(* state is R14 in the signing functions and RBX in the verification ones.   *)
(* ------------------------------------------------------------------------- *)

let PROVE_SPONGE_L1 fn sr = prove(SPONGE_L1_STMT fn sr, SPONGE_L1_TAC fn sr);;
