(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Region lemmas for the proofs of mld_H44, mld_H65 and mld_H87 of the clang *)
(* 23 -O3 build (see H_*_spec.ml), which inline the SHAKE256 of up to three  *)
(* inputs. The absorb of the first input starts at position 0 and has the    *)
(* shape of the inlined SHAKE256 of mldsa*_signature_pre_hash_shake256, for  *)
(* which x86-B's inline_sponge_*.ml have the lemmas; here they are stated    *)
(* for any registers and any offset of the state from the stack pointer      *)
(* (mld_H44 and mld_H65: data RBP, length R15, state at RSP + 16 in R14;     *)
(* mld_H87: data RBP, length R15, state at RSP in RBX). So far: the loop     *)
(* over the full blocks of 136 bytes (loop1), SPONGE_L1G.                    *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_top.ml";;
needs "x86/proofs/utils/mldsa_native_verify.ml";;
needs "x86/proofs/utils/mldsa_native_signing.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/keccakf1600_permute_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sponge_loop1.ml";;

let h_tok (kvs:(string*string) list) (s:string) =
  let rec go s (k,v) =
    let kl = String.length k in
    let b = Buffer.create (String.length s) in
    let i = ref 0 in
    while !i < String.length s do
      if !i + kl <= String.length s && String.sub s !i kl = k
      then (Buffer.add_string b v; i := !i + kl)
      else (Buffer.add_char b s.[!i]; incr i)
    done;
    Buffer.contents b in
  List.fold_left go s kvs;;

(* ------------------------------------------------------------------------- *)
(* The loop over the full blocks of 136 bytes (loop1) of an inlined SHAKE256 *)
(* absorb from position 0, as SPONGE_L1 of inline_sponge_loop1.ml, for any   *)
(* data register dr, length register lr, register sr with the address of     *)
(* the state, and offset so of the state from rsp0 (pre_hash_shake256: R12, *)
(* R13, R14 or RBX, 32; mld_H44: RBP, R15, R14, 16).                        *)
(* ------------------------------------------------------------------------- *)

let SPONGE_L1G_STMT fn dr lr sr so = parse_term(h_tok
 ["@FN@",fn; "@DR@",dr; "@LR@",lr; "@SR@",sr; "@SO@",string_of_int so;
  "@NOV@",string_of_int (296 + so + 200);
  "@SA@",(if so = 0 then "rsp0" else Printf.sprintf "word_add rsp0 (word %d)" so)]
 "exists f_events. forall e m mlen M rsp0 n (S0:1600 word) pc.
   aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   aligned 16 rsp0 /\\ mlen DIV 136 = n /\\ 0 < n /\\ mlen < 2 EXP 64 /\\
   nonoverlapping (m,mlen) (word_sub rsp0 (word 296),@NOV@) /\\
   nonoverlapping (word pc,libmldsa_size) (word_sub rsp0 (word 296),@NOV@)
   ==> ensures x86
    (\\s. bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
          read RIP s = word (pc + @FN@_loop1) /\\ read RSP s = rsp0 /\\
          read @DR@ s = m /\\ read @LR@ s = word mlen /\\
          read @SR@ s = @SA@ /\\
          read (memory :> bytes(m,mlen)) s = M /\\
          read (memory :> wbytes (@SA@)) s = S0 /\\
          read events s = e)
    (\\s. read RIP s = word (pc + @FN@_loop1_exit) /\\ read RSP s = rsp0 /\\
          read @DR@ s = word_add m (word (136 * n)) /\\
          read @LR@ s = word (mlen - 136 * n) /\\
          read @SR@ s = @SA@ /\\
          read (memory :> bytes(m,mlen)) s = M /\\
          read (memory :> wbytes (@SA@)) s =
            mld_keccak_absorb_blocks 136 S0 M n /\\
          (exists e2. read events s = APPEND e2 e /\\
             e2 = f_events m mlen rsp0 n pc /\\
             memaccess_inbounds e2
              [m,mlen; @SA@,200;
               word_sub (word_sub rsp0 (word 8)) (word 288),288;
               word_sub rsp0 (word 8),8;
               word(pc + rodata_mld_KeccakF_RoundConstants),192]
              [@SA@,200;
               word_sub (word_sub rsp0 (word 8)) (word 288),288;
               word_sub rsp0 (word 8),8]))
    (MAYCHANGE [RIP; RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [@DR@; @LR@] ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bytes(@SA@,200);
                memory :> bytes(word_sub (word_sub rsp0 (word 8)) (word 288),288);
                memory :> bytes(word_sub rsp0 (word 8),8)])");;

let SPONGE_L1G_INV dr lr sr so = parse_term(h_tok
 ["@DR@",dr; "@LR@",lr; "@SR@",sr;
  "@SA@",(if so = 0 then "rsp0" else Printf.sprintf "word_add rsp0 (word %d)" so)]
 "\\k s. read RSP s = rsp0 /\\
        read @DR@ s = word_add m (word (136 * k)) /\\
        read @LR@ s = word (mlen - 136 * k) /\\
        read @SR@ s = @SA@ /\\
        read (memory :> bytes(m,mlen)) s = M /\\
        read (memory :> wbytes (@SA@)) s =
          mld_keccak_absorb_blocks 136 S0 M k");;

let SPONGE_ALIGN_FACTS_G so = FIRST_ASSUM(fun ra -> if concl ra = `aligned 16 (rsp0:int64)` then
   MAP_EVERY (fun k -> ASSUME_TAC (MATCH_MP ALIGNED_WORD_ADD (CONJ ra (SPONGE_A16 k)))) (map (fun j -> so + 16 * j) (0--8))
   else NO_TAC);;

let SPONGE_L1G_BODY fn lr so =
    let lrc = mk_const(lr,[]) in
    let wtm = if so = 0 then `read (memory :> wbytes (rsp0:int64)) s30 = word_xor XX (word BLK:1600 word)`
              else subst [mk_small_numeral so,`SO:num`] `read (memory :> wbytes (word_add rsp0 (word SO))) s30 = word_xor XX (word BLK:1600 word)` in
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
    SPONGE_ALIGN_FACTS_G so THEN
    YMM_GHOST_TAC `s0:x86state` ["YMM0","y0"; "YMM1","y1"] THEN
    X86_STEPS_TAC (SPONGE_L1_EXEC fn) (1--30) THEN
    SPONGE_LANE_FACTS "s30" THEN SPONGE_HI_FACTS THEN
    SUBGOAL_THEN wtm ASSUME_TAC THENL
     [MATCH_MP_TAC READ_MEMORY_WBYTES_OF_LANES THEN
      CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[WORD_ADD_0] THEN REPEAT CONJ_TAC THEN
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
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(fun a -> if can (term_match [] (mk_eq(list_mk_icomb "read" [lrc; `s33:x86state`],`x:int64`))) (concl a) then REWRITE_RULE[th] a else a)) THEN
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

let SPONGE_L1G_TAC fn dr lr sr so =
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
   (parse_term (Printf.sprintf "pc + %s_loop1_exit" fn)) (SPONGE_L1G_INV dr lr sr so) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `0 < n` THEN ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[mld_keccak_absorb_blocks; MULT_CLAUSES; WORD_ADD_0; SUB_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    SPONGE_L1G_BODY fn lr so;
    FULL_EXIT0_TAC];;

let PROVE_SPONGE_L1G fn dr lr sr so = prove(SPONGE_L1G_STMT fn dr lr sr so, SPONGE_L1G_TAC fn dr lr sr so);;

(* The instances, the loop over the blocks of the first input of mld_H, are  *)
(* proved where they are used: PROVE_SPONGE_L1G "mld_H44" "RBP" "R15" "R14"  *)
(* 16 (also mld_H65) and PROVE_SPONGE_L1G "mld_H87" "RBP" "R15" "RBX" 0.     *)
