(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The SHAKE256 of a message that clang 23 inlines into mldsa{44,65,87}_     *)
(* signature_pre_hash_shake256 and mldsa{44,65,87}_verify_pre_hash_          *)
(* shake256, as a lemma from its first instruction (+0x2e, after the         *)
(* arguments have been saved) to +0x2bb: the zeroing of the state at rsp +   *)
(* 0x20, the absorbing of the message of mlen bytes, the padding and         *)
(* permutation, and the copy of the first 64 bytes of the output to rsp +    *)
(* 0x180, after which the code clears the state again. The lemmas are for    *)
(* the pieces (SPONGE_ZERO, SPONGE_J1 for the full blocks, the tail lemma of *)
(* inline_sponge_tail_glue.ml, SPONGE_FIN) and SPONGE_REGION, which puts     *)
(* them together and states the digest as in the specifications, with        *)
(* mld_shake256_byte of common/mldsa_native_fips202.ml.                      *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sponge_loop1.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sponge_tail_glue.ml";;

(* ------------------------------------------------------------------------- *)
(* Lemmas about bytes and chunks of the state.                               *)
(* ------------------------------------------------------------------------- *)

(*** The byte j of a state XORed with the constant c at byte r ***)

let SPONGE_BYTE_AT = prove(`!(Y:1600 word) r j c.
     r < 200 /\ j < 200 /\ c < 256
     ==> word_subword (word_xor Y (word (2 EXP (8 * r) * c))) (8 * j,8):byte =
         if j = r then word_xor (word_subword Y (8 * j,8)) (word c)
         else word_subword Y (8 * j,8)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  ASM_SIMP_TAC[WORD_SUBWORD_WORD; DIMINDEX_CONV `dimindex(:1600)`; DIMINDEX_8;
               ARITH_RULE `j < 200 ==> 8 * j + 8 <= 1600`] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`] THEN
  MP_TAC(SPECL [`0`; `c:num`; `r:num`; `j:num`] SPONGE_BYTE_UPDATE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[LT_NZ; EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[];
    REWRITE_TAC[DIV_0; MOD_0; WORD_XOR_0]]);;

(*** A state that is zero in chunks of 128 bits and in its last 8 bytes ***)

let SPONGE_ZERO_BYTES = prove
 (`!(a:int64) (s:x86state).
     (!c. c < 12 ==> read (memory :> bytes128 (word_add a (word (16 * c)))) s = word 0) /\
     (!k. k < 8 ==> read (memory :> bytes8 (word_add a (word (192 + k)))) s = word 0)
     ==> !j. j < 200 ==> read (memory :> bytes8 (word_add a (word j))) s = word 0`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    let h1 = CONJUNCT1 th and h2 = CONJUNCT2 th in
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_CASES_TAC `j < 192` THENL
     [MP_TAC(SPEC `j DIV 16` h1) THEN
      ANTS_TAC THENL [UNDISCH_TAC `j < 192` THEN ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(fun th ->
        MP_TAC(MATCH_MP SPONGE_BYTES8_OF_CHUNK128 (CONJ th (ARITH_RULE `j MOD 16 < 16`)))) THEN
      SUBGOAL_THEN `word_add (word_add a (word (16 * (j DIV 16)))) (word (j MOD 16)):int64 = word_add a (word j)` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[WORD_SUBWORD_0];
      MP_TAC(SPEC `j - 192` h2) THEN
      ANTS_TAC THENL [UNDISCH_TAC `j < 200` THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `192 + (j - 192) = j` SUBST1_TAC THENL [UNDISCH_TAC `~(j < 192)` THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[]]));;

let SPONGE_XMM0_ZERO = prove(`!(x:128 word). word_subword (word_join x (word 0:128 word):256 word) (0,128):128 word = word 0`, GEN_TAC THEN BITBLAST_TAC);;
let SPONGE_XMM_LOW = prove(`!(a:128 word) (b:128 word). word_subword (word_join a b:256 word) (0,128):128 word = b`, REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(*** The 64 bytes at a, as four chunks of 128 bits of a state K ***)

let SPONGE_SUBWORD512_BYTE = prove(`!(K:1600 word) j. j < 64 ==> word ((val (word_subword K (0,512):512 word) DIV 2 EXP (8 * j)) MOD 256):byte = word_subword K (8 * j,8)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `MIN 8 (512 - 8*j) = 8` ASSUME_TAC THENL [UNDISCH_TAC `j < 64` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`K:1600 word`; `0`; `512`; `8 * j`; `8`] (INST_TYPE [`:512`,`:N`; `:1600`,`:M`; `:8`,`:P`] WORD_SUBWORD_SUBWORD)) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`; DIMINDEX_8; DIMINDEX_512; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[word_subword; DIMINDEX_8; DIMINDEX_512; VAL_WORD; DIV_1; MOD_MOD_REFL; ARITH_RULE `2 EXP 8 = 256`] THEN
  AP_TERM_TAC THEN
  MP_TAC(SPECL [`val(K:1600 word)`; `512`; `j:num`] SPONGE_MODDIV_BYTE) THEN
  ANTS_TAC THENL [UNDISCH_TAC `j < 64` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`; EXP; DIV_1]);;

(* one chunk of 128 bits of four, byte r of chunk q *)
let SPONGE_CHUNK_AT = prove(`!(a:int64) (K:1600 word) (s:x86state) q r.
     read (memory :> bytes128 (word_add a (word (16 * q)))) s = word_subword K (128 * q,128) /\ q < 4 /\ r < 16
     ==> read (memory :> bytes8 (word_add a (word (16 * q + r)))) s = word_subword K (8 * (16 * q + r),8)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`word_add (a:int64) (word (16 * q))`; `word_subword (K:1600 word) (128 * q,128):int128`; `r:num`; `s:x86state`] SPONGE_BYTES8_OF_CHUNK128) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `word_add (word_add (a:int64) (word (16 * q))) (word r) = word_add a (word (16 * q + r))` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`K:1600 word`; `q:num`; `r:num`] SPONGE_SUBSUB128) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ARITH_RULE `8 * (16 * q + r) = 128 * q + 8 * r`]);;

let SPONGE_BYTES_OF_CHUNKS4 = prove
 (`!(a:int64) (K:1600 word) (s:x86state).
     read (memory :> bytes128 a) s = word_subword K (0,128) /\
     read (memory :> bytes128 (word_add a (word 16))) s = word_subword K (128,128) /\
     read (memory :> bytes128 (word_add a (word 32))) s = word_subword K (256,128) /\
     read (memory :> bytes128 (word_add a (word 48))) s = word_subword K (384,128)
     ==> read (memory :> bytes(a,64)) s = val(word_subword K (0,512):512 word)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word_subword (K:1600 word) (0,512):512 word) = val(word_subword K (0,512):512 word) MOD 2 EXP (8 * 64)` SUBST1_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(ISPEC `word_subword (K:1600 word) (0,512):512 word` VAL_BOUND) THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC READ_MEMORY_BYTES_OF_BYTES8 THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[SPONGE_SUBWORD512_BYTE] THEN
  MP_TAC(SPECL [`a:int64`; `K:1600 word`; `s:x86state`; `j DIV 16`; `j MOD 16`] SPONGE_CHUNK_AT) THEN
  SUBGOAL_THEN `16 * (j DIV 16) + j MOD 16 = j` (fun th -> REWRITE_TAC[th]) THENL [ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `j DIV 16 < 4` MP_TAC THENL [UNDISCH_TAC `j < 64` THEN ARITH_TAC; ALL_TAC] THEN
      SPEC_TAC(`j DIV 16`,`q:num`) THEN
      REWRITE_TAC[ARITH_RULE `q < 4 <=> q = 0 \/ q = 1 \/ q = 2 \/ q = 3`] THEN
      GEN_TAC THEN DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[WORD_ADD_0];
      UNDISCH_TAC `j < 64` THEN ARITH_TAC];
    DISCH_THEN ACCEPT_TAC]);;


(*** The 64 bytes at a from the four chunks of 128 bits of a number below   ***)
(*** 2^512, as the code of the callers loads and stores them                ***)

let API_BYTES64_OF_CHUNKS = prove
 (`!(a:int64) (s:x86state) x.
        x < 2 EXP 512 /\
        read (memory :> bytes128 a) s = word ((x DIV 2 EXP (128 * 0)) MOD 2 EXP 128) /\
        read (memory :> bytes128 (word_add a (word 16))) s =
          word ((x DIV 2 EXP (128 * 1)) MOD 2 EXP 128) /\
        read (memory :> bytes128 (word_add a (word 32))) s =
          word ((x DIV 2 EXP (128 * 2)) MOD 2 EXP 128) /\
        read (memory :> bytes128 (word_add a (word 48))) s =
          word ((x DIV 2 EXP (128 * 3)) MOD 2 EXP 128)
        ==> read (memory :> bytes(a,64)) s = x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x < 2 EXP 1600` ASSUME_TAC THENL
   [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 512` THEN ASM_REWRITE_TAC[LE_EXP] THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SPONGE_NUM_SUBWORD128 (ASSUME `x < 2 EXP 1600`)]) THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_MULT_CONV)) THEN
  MP_TAC(SPECL [`a:int64`; `word x:1600 word`; `s:x86state`] SPONGE_BYTES_OF_CHUNKS4) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_CONV `dimindex(:1600)`; DIMINDEX_CONV `dimindex(:512)`; EXP; DIV_1; VAL_WORD] THEN
  REWRITE_TAC[ARITH_RULE `MIN 512 512 = 512`] THEN
  SUBGOAL_THEN `x MOD 2 EXP 1600 = x` SUBST1_TAC THENL [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]);;
(* ------------------------------------------------------------------------- *)
(* The zeroing of the state: from +0x2e (the XORPS that clears XMM0) to the  *)
(* comparison of the length with 136 (+0x87), 13 stores of 16 bytes, the     *)
(* first of which (at rsp + 0xdc) also covers the 4 bytes after the state.   *)
(* It changes only XMM0, the memory and the events, so that the callers can  *)
(* rely on RDX and the other registers.                                      *)
(* ------------------------------------------------------------------------- *)

let SPONGE_ZERO_STMT fn = parse_term(Printf.sprintf
 "exists f_events. forall e rsp0 pc.
   aligned 16 rsp0 /\\ aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   nonoverlapping (word pc,libmldsa_size) (word_add rsp0 (word 32),204)
   ==> ensures x86
     (\\s. bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
          read RIP s = word (pc + %d) /\\
          read RSP s = rsp0 /\\ read events s = e)
     (\\s. read RIP s = word (pc + %d) /\\
          read RSP s = rsp0 /\\
          read (memory :> wbytes (word_add rsp0 (word 32))) s = (word 0:1600 word) /\\
          (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 pc /\\
             memaccess_inbounds e2 [word_add rsp0 (word 32),204] [word_add rsp0 (word 32),204]))
     (MAYCHANGE [RIP] ,, MAYCHANGE [ZMM0] ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(word_add rsp0 (word 32),204)])"
  (layout fn + 46) (layout fn + 135));;

let SPONGE_ZERO_TAC fn =
  let exec = SPONGE_TAIL_EXEC fn in
  CONCRETIZE_F_EVENTS_TAC `\(rsp0:int64) (pc:num). f_ev_z rsp0 pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN
  YMM_GHOST_TAC `s0:x86state` ["YMM0","y0"] THEN
  FIRST_ASSUM(fun ra -> if concl ra = `aligned 16 (rsp0:int64)` then MAP_EVERY (fun k -> ASSUME_TAC (MATCH_MP ALIGNED_WORD_ADD (CONJ ra (SPONGE_A16 k)))) [32;48;64;80;96;112;128;144;160;176;192;208] else NO_TAC) THEN
  X86_STEPS_TAC exec (1--2) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPONGE_XMM0_ZERO]) THEN
  FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes128 (word_add rsp0 (word 220))) s2 = x`) (concl th) then
    MAP_EVERY (fun k ->
      let f = MATCH_MP SPONGE_BYTES8_OF_CHUNK128 (CONJ th (ARITH_RULE(mk_binop `(<):num->num->bool` (mk_small_numeral k) `16`))) in
      let f' = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC DEPTH_CONV NUM_ADD_CONV) f in
      ASSUME_TAC(REWRITE_RULE[WORD_SUBWORD_0] f')) (4--11)
    else NO_TAC) THEN
  X86_STEPS_TAC exec (3--14) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPONGE_XMM0_ZERO]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SPONGE_WBYTES_OF_ALL_BYTES THEN
    REWRITE_TAC[WORD_SUBWORD_0] THEN
    MATCH_MP_TAC SPONGE_ZERO_BYTES THEN CONJ_TAC THENL
     [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[SPONGE_BYTES32_ADDR] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[SPONGE_BYTES32_ADDR] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]];
    DISCHARGE_SAFETY_PROPERTY_TAC];;

(* ------------------------------------------------------------------------- *)
(* The end: the padding of the state after the last r < 136 bytes (0x1F at   *)
(* byte r, 0x80 at byte 135), the permutation, the copy of the first 64      *)
(* bytes of the state to rsp + 0x180 (384 from rsp0 + 0) and the clearing    *)
(* of the state, from join5 to +0x2bb.                                       *)
(* ------------------------------------------------------------------------- *)

let SPONGE_FIN_STMT fn sr = parse_term(Printf.sprintf
 "exists f_events. forall e r (Y:1600 word) rsp0 pc.
   r < 136 /\\ aligned 16 rsp0 /\\
   aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   nonoverlapping (word pc,libmldsa_size) (word_sub rsp0 (word 296),744) /\\
   nonoverlapping (word_add rsp0 (word 32),200) (word_add rsp0 (word 232),4) /\\
   nonoverlapping (word_add rsp0 (word 32),224) (word_add rsp0 (word 384),64) /\\
   nonoverlapping (word_sub rsp0 (word 296),296) (word_add rsp0 (word 32),224) /\\
   nonoverlapping (word_sub rsp0 (word 296),296) (word_add rsp0 (word 384),64)
   ==> ensures x86
     (\\s. bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
          read RIP s = word (pc + %s_join5) /\\
          read RSP s = rsp0 /\\ read R13 s = word r /\\
          read (memory :> wbytes (word_add rsp0 (word 32))) s = Y /\\
          read events s = e)
     (\\s. read RIP s = word (pc + %d) /\\
          read RSP s = rsp0 /\\
          read (memory :> bytes(word_add rsp0 (word 384),64)) s =
            val (word_subword (keccak_f1600
                   (word_xor (word_xor Y (word (2 EXP (8 * r) * 31)))
                             (word (2 EXP (8 * 135) * 128)):1600 word)) (0,512):512 word) /\\
          (exists e2. read events s = APPEND e2 e /\\ e2 = f_events r rsp0 pc /\\
             memaccess_inbounds e2
              [word_add rsp0 (word 32),208; word_add rsp0 (word 384),64;
               word_sub (word_sub rsp0 (word 8)) (word 288),288;
               word_sub rsp0 (word 8),8; word(pc + rodata_mld_KeccakF_RoundConstants),192]
              [word_add rsp0 (word 32),208; word_add rsp0 (word 384),64;
               word_sub (word_sub rsp0 (word 8)) (word 288),288;
               word_sub rsp0 (word 8),8]))
     (MAYCHANGE [RIP; RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [R12; R13; %s] ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(word_add rsp0 (word 32),208);
                 memory :> bytes(word_add rsp0 (word 384),64);
                 memory :> bytes(word_sub (word_sub rsp0 (word 8)) (word 288),288);
                 memory :> bytes(word_sub rsp0 (word 8),8)])"
  fn (layout fn + 699) sr);;

let SPONGE_FIN_NORM = CONV_RULE(DEPTH_CONV(fun tm -> match tm with Comb(Comb(Const("word_add",_),a),Comb(Const("word",_),n)) when not(is_numeral n) && can NUM_REDUCE_CONV n -> RAND_CONV(RAND_CONV NUM_REDUCE_CONV) tm | _ -> failwith "SPONGE_FIN_NORM"));;

let SPONGE_RESTRICT_NE t th =
  let j,bod = dest_forall(concl th) in
  let p,q = dest_imp bod in
  let p' = mk_conj(p,mk_neg(mk_eq(j,t))) in
  GEN j (DISCH p' (MP (SPEC j th) (CONJUNCT1(ASSUME p'))));;

let SPONGE_FIN_STEP1_FACTS =
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && free_in `bytes8` (concl th) && free_in `s1:x86state` (concl th) then
      ASSUME_TAC(SPONGE_RESTRICT_NE `r:num` th) THEN
      ASSUME_TAC(MP (SPEC `r:num` th) (ASSUME `r < 200`))
    else NO_TAC) THEN
  SUBGOAL_THEN `read (memory :> bytes8 (word_add rsp0 (word (1 * r + 32)))) s1 = word_subword (Y:1600 word) (8 * r,8)` ASSUME_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC];;

let SPONGE_FIN_VARS = [`r:num`; `Y:1600 word`; `rsp0:int64`; `pc:num`];;

let SPONGE_FIN_TAC fn =
  let exec = SPONGE_TAIL_EXEC fn in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   (SPONGE_RENAME_E2 MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600)
   "H_PERMUTE" THEN
  CONCRETIZE_F_EVENTS_TAC `\(r:num) (rsp0:int64) (pc:num). f_ev_f r rsp0 pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `r:num`; `Y:1600 word`; `rsp0:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; NONOVERLAPPING_CLAUSES; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN
  MP_TAC(MATCH_MP TG_VALR (ASSUME `r < 136`)) THEN DISCH_TAC THEN
  (* the bytes of the state, the first two XORs *)
  FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> wbytes a) s0 = X`) (concl th) then ASSUME_TAC(MATCH_MP SPONGE_ALL_BYTES_OF_WBYTES32 th) else NO_TAC) THEN
  X86_STEPS_TAC exec (1--1) THEN
  SUBGOAL_THEN `r < 200` ASSUME_TAC THENL [UNDISCH_TAC `r < 136` THEN ARITH_TAC; ALL_TAC] THEN
  SPONGE_FIN_STEP1_FACTS THEN X86_STEPS_TAC exec (2--2) THEN
  SUBGOAL_THEN `!j. j < 200 ==> read (memory :> bytes8 (word_add rsp0 (word (j + 32)))) s2 = word_subword (word_xor (Y:1600 word) (word (2 EXP (8 * r) * 31))) (8 * j,8)` ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`Y:1600 word`; `r:num`; `j:num`; `31`] SPONGE_BYTE_AT) THEN
    ANTS_TAC THENL [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ARITH_TAC]]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM(fun th -> if concl th = `(j:num) = r` then SUBST_ALL_TAC th else NO_TAC) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(fun th -> if is_forall(concl th) && free_in `bytes8` (concl th) && free_in `s2:x86state` (concl th) && can (find_term is_neg) (concl th)
        then ACCEPT_TAC(MP (SPEC `j:num` th) (CONJ (ASSUME `j < 200`) (ASSUME `~((j:num) = r)`))) else NO_TAC)];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && free_in `bytes8` (concl th) && free_in `s2:x86state` (concl th) && not(can (find_term is_neg) (concl th)) then
      ASSUME_TAC(SPONGE_RESTRICT_NE `135` th) THEN
      ASSUME_TAC(REWRITE_RULE[ARITH_RULE `135 + 32 = 167`; ARITH_RULE `8 * 135 = 1080`] (MP (SPEC `135` th) (ARITH_RULE `135 < 200`)))
    else NO_TAC) THEN
  X86_STEPS_TAC exec (3--3) THEN
  SUBGOAL_THEN `!j. j < 200 ==> read (memory :> bytes8 (word_add rsp0 (word (j + 32)))) s3 = word_subword (word_xor (word_xor (Y:1600 word) (word (2 EXP (8 * r) * 31))) (word (2 EXP (8 * 135) * 128))) (8 * j,8)` ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`word_xor (Y:1600 word) (word (2 EXP (8 * r) * 31))`; `135`; `j:num`; `128`] SPONGE_BYTE_AT) THEN
    ANTS_TAC THENL [CONJ_TAC THENL [ARITH_TAC; CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ARITH_TAC]]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM(fun th -> if concl th = `(j:num) = 135` then SUBST_ALL_TAC th else NO_TAC) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `135 + 32 = 167`; ARITH_RULE `8 * 135 = 1080`]) THEN
      REWRITE_TAC[ARITH_RULE `135 + 32 = 167`; ARITH_RULE `8 * 135 = 1080`] THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(fun th -> if is_forall(concl th) && free_in `bytes8` (concl th) && free_in `s3:x86state` (concl th) && can (find_term is_neg) (concl th)
        then ACCEPT_TAC(MP (SPEC `j:num` th) (CONJ (ASSUME `j < 200`) (ASSUME `~((j:num) = 135)`))) else NO_TAC)];
    ALL_TAC] THEN
  X86_STEPS_TAC exec (4--7) THEN
  SUBGOAL_THEN `read (memory :> wbytes (word_add rsp0 (word 32))) s7 = word_xor (word_xor (Y:1600 word) (word (2 EXP (8 * r) * 31))) (word (2 EXP (8 * 135) * 128))` ASSUME_TAC THENL
   [MATCH_MP_TAC SPONGE_WBYTES32_OF_ALL_BYTES THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  (* the permutation *)
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc exec "H_PERMUTE"
   [`read RDI s`; `word_xor (word_xor (Y:1600 word) (word (2 EXP (8 * r) * 31))) (word (2 EXP (8 * 135) * 128))`;
    `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`] SPONGE_FIN_VARS 8 THEN
  (* the copy and the clearing *)
  FIRST_ASSUM(fun ra -> if concl ra = `aligned 16 (rsp0:int64)` then
     MAP_EVERY (fun k -> ASSUME_TAC (MATCH_MP ALIGNED_WORD_ADD (CONJ ra (SPONGE_A16 k)))) [32;48;64;80;96;112;128;144;160;176;192;208;224;384;400;416;432] else NO_TAC) THEN
  FIRST_ASSUM(fun wth -> if can (term_match [] `read (memory :> wbytes (word_add rsp0 (word 32))) s8 = X`) (concl wth) then
    MAP_EVERY (fun k ->
      let c = MATCH_MP READ_MEMORY_BYTES128_OF_WBYTES (CONJ wth (ARITH_RULE(mk_binop `(<):num->num->bool` (mk_small_numeral k) `12`))) in
      ASSUME_TAC(SPONGE_FIN_NORM(REWRITE_RULE[SPONGE_BYTES32_ADDR] c))) [0;1;2;3]
    else NO_TAC) THEN
  YMM_GHOST_TAC `s8:x86state` ["YMM0","y0"; "YMM1","y1"; "YMM2","y2"; "YMM3","y3"] THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && name_of(fst(strip_comb(snd(dest_imp(snd(strip_forall(concl th))))))) = "ensures" then ALL_TAC else NO_TAC) THEN
  SUBGOAL_THEN `word_add (word_sub (rsp0:int64) (word 8)) (word 8) = rsp0` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC `KK:1600 word = keccak_f1600 (word_xor (word_xor (Y:1600 word) (word (2 EXP (8 * r) * 31))) (word (2 EXP (8 * 135) * 128)))` THEN
  X86_STEPS_TAC exec (9--30) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPONGE_XMM_LOW]) THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SPONGE_BYTES_OF_CHUNKS4 THEN
    REWRITE_TAC[WORD_RULE `word_add (word_add (a:int64) (word 384)) (word 16) = word_add a (word 400)`;
                WORD_RULE `word_add (word_add (a:int64) (word 384)) (word 32) = word_add a (word 416)`;
                WORD_RULE `word_add (word_add (a:int64) (word 384)) (word 48) = word_add a (word 432)`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes128 a) s30 = x`) (concl th) then (MP_TAC th THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN NO_TAC) else NO_TAC);
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let PROVE_SPONGE_ZERO fn = prove(SPONGE_ZERO_STMT fn, SPONGE_ZERO_TAC fn);;
let PROVE_SPONGE_FIN fn sr = prove(SPONGE_FIN_STMT fn sr, SPONGE_FIN_TAC fn);;

(* ------------------------------------------------------------------------- *)
(* The digest in the form of the specifications, and the state that the C    *)
(* code has before the permutation.                                          *)
(* ------------------------------------------------------------------------- *)

let SPONGE_NBL_SEQ = prove(`!(K:1600 word) n. n <= 200 ==> num_of_bytelist(list_of_seq (\j. word_subword K (8*j,8):byte) n) = val K MOD 2 EXP (8*n)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[list_of_seq; num_of_bytelist; MULT_CLAUSES; EXP; MOD_1]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `n <= 200` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th))) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[list_of_seq; NUM_OF_BYTELIST_APPEND; LENGTH_LIST_OF_SEQ; num_of_bytelist] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_CONV `dimindex(:1600)`; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPECL [`val(K:1600 word)`; `2 EXP (8 * n)`; `256`] MOD_MULT_MOD) THEN
  REWRITE_TAC[ARITH_RULE `8 * SUC n = 8 * n + 8`; EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let SPONGE_SHAKE256_DIGEST = prove(`!mlen M. num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64) = val(word_subword (keccak_f1600 (mld_shake256_state mlen M)) (0,512):512 word)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `list_of_seq (mld_shake256_byte mlen M) 64 = list_of_seq (\j. word_subword (keccak_f1600 (mld_shake256_state mlen M)) (8*j,8):byte) 64` SUBST1_TAC THENL
   [MATCH_MP_TAC LIST_OF_SEQ_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[mld_shake256_byte; mld_keccak_squeeze_byte] THEN
    SUBGOAL_THEN `(136 + i) DIV 136 = 1 /\ (136 + i) MOD 136 = i` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `i:num`; MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1`] THEN UNDISCH_TAC `i < 64` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `1 = SUC 0`; keccak_squeeze];
    ALL_TAC] THEN
  MP_TAC(SPECL [`keccak_f1600 (mld_shake256_state mlen M)`; `64`] SPONGE_NBL_SEQ) THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_CONV `dimindex(:1600)`; DIMINDEX_CONV `dimindex(:512)`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[EXP; DIV_1]);;

let SPONGE_SHAKE_STATE = prove(`!M n r R.
     r < 136 /\ R = (M DIV 2 EXP (8 * 136 * n)) MOD 2 EXP (8 * r) /\
     M < 2 EXP (8 * (136 * n + r))
     ==> mld_shake256_state (136 * n + r) M =
         word_xor (word_xor (word_xor (mld_keccak_absorb_blocks 136 (word 0) M n) (word R))
                            (word (2 EXP (8 * r) * 31)))
                  (word (2 EXP (8 * 135) * 128)):1600 word`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(136 * n + r) DIV 136 = n /\ (136 * n + r) MOD 136 = r` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `r:num`; MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `n:num`] THEN
    UNDISCH_TAC `r < 136` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `M DIV 2 EXP (8 * 136 * n) < 2 EXP (8 * r)` ASSUME_TAC THENL
   [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[GSYM EXP_ADD] THEN
    SUBGOAL_THEN `8 * 136 * n + 8 * r = 8 * (136 * n + r)` (fun th -> REWRITE_TAC[th]) THENL
     [ARITH_TAC; FIRST_ASSUM ACCEPT_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `R = M DIV 2 EXP (8 * 136 * n)` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(fun th -> if concl th = `R = (M DIV 2 EXP (8 * 136 * n)) MOD 2 EXP (8 * r)` then SUBST1_TAC th else NO_TAC) THEN MATCH_MP_TAC MOD_LT THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(M DIV 2 EXP (8 * 136 * n)) MOD 2 EXP (8 * 136) = M DIV 2 EXP (8 * 136 * n)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP (8 * r)` THEN
    ASM_REWRITE_TAC[LE_EXP] THEN UNDISCH_TAC `r < 136` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[mld_shake256_state; mld_keccak_finalize; mld_keccak_absorb; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[FST; SND] THEN
  REWRITE_TAC[ARITH_RULE `8 * 0 = 0`; EXP; MULT_CLAUSES; ADD_CLAUSES; ARITH_RULE `136 - 1 = 135`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* From the comparison of the length with 136 (+0x87) to join1: if there are *)
(* full blocks, loop1 absorbs them, as in inline_sponge_loop1.ml; otherwise  *)
(* the state stays zero. R12 and R13 are the rest of the message and its     *)
(* length then.                                                              *)
(* ------------------------------------------------------------------------- *)

let SPONGE_J1_STMT fn sr = parse_term(Printf.sprintf
 "exists f_events. forall e m mlen M rsp0 pc.
   aligned 16 rsp0 /\\ aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   mlen < 2 EXP 64 /\\
   nonoverlapping (m,mlen) (word_sub rsp0 (word 296),528) /\\
   nonoverlapping (word pc,libmldsa_size) (word_sub rsp0 (word 296),528)
   ==> ensures x86
    (\\s. bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
          read RIP s = word (pc + %d) /\\ read RSP s = rsp0 /\\
          read R12 s = m /\\ read R13 s = word mlen /\\ read RDX s = word mlen /\\
          read (memory :> bytes(m,mlen)) s = M /\\
          read (memory :> wbytes (word_add rsp0 (word 32))) s = (word 0:1600 word) /\\
          read events s = e)
    (\\s. read RIP s = word (pc + %s_join1) /\\ read RSP s = rsp0 /\\
          read R12 s = word_add m (word (136 * (mlen DIV 136))) /\\
          read R13 s = word (mlen - 136 * (mlen DIV 136)) /\\
          read (memory :> bytes(m,mlen)) s = M /\\
          read (memory :> wbytes (word_add rsp0 (word 32))) s =
            mld_keccak_absorb_blocks 136 (word 0) M (mlen DIV 136) /\\
          (exists e2. read events s = APPEND e2 e /\\
             e2 = f_events m mlen rsp0 pc /\\
             memaccess_inbounds e2
              [m,mlen; word_add rsp0 (word 32),200;
               word_sub (word_sub rsp0 (word 8)) (word 288),288;
               word_sub rsp0 (word 8),8;
               word(pc + rodata_mld_KeccakF_RoundConstants),192]
              [word_add rsp0 (word 32),200;
               word_sub (word_sub rsp0 (word 8)) (word 288),288;
               word_sub rsp0 (word 8),8]))
    (MAYCHANGE [RIP; RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [R12; R13; %s] ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bytes(word_add rsp0 (word 32),200);
                memory :> bytes(word_sub (word_sub rsp0 (word 8)) (word 288),288);
                memory :> bytes(word_sub rsp0 (word 8),8)])"
  (layout fn + 135) fn sr);;

let SPONGE_J1_VARS = [`m:int64`; `mlen:num`; `M:num`; `rsp0:int64`; `pc:num`];;

let SPONGE_J1_TAC fn l1 =
  let exec = SPONGE_TAIL_EXEC fn in
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 l1) "H_L1" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(m:int64) (mlen:num) (rsp0:int64) (pc:num).
      if mlen < 136 then f_ev_a m mlen rsp0 pc else f_ev_b m mlen rsp0 pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `m:int64`; `mlen:num`; `M:num`; `rsp0:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; NONOVERLAPPING_CLAUSES; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN
  ASM_CASES_TAC `mlen < 136` THENL
   [(*** no full block: the state stays zero ***)
    X86_STEPS_TAC exec (1--2) THEN
    TG_RES [MATCH_MP TG_VALR2 (ASSUME `mlen < 136`); ASSUME `mlen < 136`] THEN
    SUBGOAL_THEN `mlen DIV 136 = 0` ASSUME_TAC THENL [MATCH_MP_TAC DIV_LT THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[mld_keccak_absorb_blocks; MULT_CLAUSES; WORD_ADD_0; SUB_0] THEN
    DISCHARGE_SAFETY_PROPERTY_SPINE_TAC;
    (*** the blocks of loop1 ***)
    SUBGOAL_THEN `val (word mlen:int64) = mlen` ASSUME_TAC THENL [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    X86_STEPS_TAC exec (1--2) THEN TG_RES [ASSUME `val (word mlen:int64) = mlen`; ASSUME `~(mlen < 136)`] THEN
    X86_STEPS_TAC exec (3--4) THEN
    SUBGOAL_THEN `0 < mlen DIV 136` ASSUME_TAC THENL [UNDISCH_TAC `~(mlen < 136)` THEN ARITH_TAC; ALL_TAC] THEN
    FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc exec "H_L1"
     [`m:int64`; `mlen:num`; `M:num`; `rsp0:int64`; `mlen DIV 136`; `word 0:1600 word`; `pc:num`] SPONGE_J1_VARS 5 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_SPINE_TAC];;

let PROVE_SPONGE_J1 fn sr l1 = prove(SPONGE_J1_STMT fn sr, SPONGE_J1_TAC fn l1);;

(* ------------------------------------------------------------------------- *)
(* The digest in the form that the specifications use, from the state that   *)
(* the pieces leave: the blocks absorbed by loop1, the XOR of the last r     *)
(* bytes of the message, and the padding.                                    *)
(* ------------------------------------------------------------------------- *)

let SPONGE_NOV_OFFSET = prove(`!(a:int64) (b:int64) n k d l.
     nonoverlapping_modulo (2 EXP 64) (val a,n) (val b,k) /\ d + l <= n
     ==> nonoverlapping_modulo (2 EXP 64) (val (word_add a (word d)),l) (val b,k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nonoverlapping_modulo; NOT_EXISTS_THM] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`d + i:num`; `j:num`]) THEN
  SUBGOAL_THEN `d + i < n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(val (word_add (a:int64) (word d)) + i == val (b:int64) + j) (mod (2 EXP 64))` THEN
  REWRITE_TAC[CONG; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[ADD_ASSOC]);;

let SPONGE_NOV_SUB2 = prove(`!(a:int64) (b:int64) n k d l e p.
     nonoverlapping_modulo (2 EXP 64) (val a,n) (val b,k) /\ d + l <= n /\ e + p <= k
     ==> nonoverlapping_modulo (2 EXP 64) (val (word_add a (word d)),l)
                                          (val (word_add b (word e)),p)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN
  MATCH_MP_TAC SPONGE_NOV_OFFSET THEN EXISTS_TAC `k:num` THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN
  MATCH_MP_TAC SPONGE_NOV_OFFSET THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]);;

let SPONGE_REGION_LINK = prove(`!mlen M.
     M < 2 EXP (8 * mlen)
     ==> val (word_subword
           (keccak_f1600
             (word_xor
               (word_xor
                 (word_xor (mld_keccak_absorb_blocks 136 (word 0) M (mlen DIV 136))
                           (word ((M DIV 2 EXP (8 * (136 * (mlen DIV 136))))
                                  MOD 2 EXP (8 * (mlen - 136 * (mlen DIV 136))))))
                 (word (2 EXP (8 * (mlen - 136 * (mlen DIV 136))) * 31)))
               (word (2 EXP (8 * 135) * 128)):1600 word)) (0,512):512 word) =
         num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SPONGE_SHAKE256_DIGEST] THEN
  MP_TAC(SPECL [`M:num`; `mlen DIV 136`; `mlen - 136 * (mlen DIV 136)`;
                `(M DIV 2 EXP (8 * (136 * (mlen DIV 136)))) MOD 2 EXP (8 * (mlen - 136 * (mlen DIV 136)))`]
         SPONGE_SHAKE_STATE) THEN
  SUBGOAL_THEN `136 * (mlen DIV 136) + (mlen - 136 * (mlen DIV 136)) = mlen /\ mlen - 136 * (mlen DIV 136) < 136` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`mlen:num`; `136`] DIVISION) THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `8 * 136 * n = 8 * (136 * n)`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* ------------------------------------------------------------------------- *)
(* The whole SHAKE256 of the message at m, from +0x2e to +0x2bb: the zeroing, *)
(* the blocks, the rest of the message and the end. The state of 200 bytes   *)
(* is at rsp0 + 32, the digest of 64 bytes (the argument of the following    *)
(* code) is left at rsp0 + 384, the state is zero again and the frame below  *)
(* rsp0 is that of mldsa_keccakf1600_permute. The callers keep the           *)
(* arguments in RDX, R12 and R13 until this point.                           *)
(* ------------------------------------------------------------------------- *)

let SPONGE_REGION_STMT fn sr = parse_term(Printf.sprintf
 "exists f_events. forall e m mlen M rsp0 pc.
   aligned 16 rsp0 /\\ aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   mlen < 2 EXP 64 /\\
   nonoverlapping (m,mlen) (word_sub rsp0 (word 296),744) /\\
   nonoverlapping (word pc,libmldsa_size) (word_sub rsp0 (word 296),744)
   ==> ensures x86
    (\\s. bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
          read RIP s = word (pc + %d) /\\ read RSP s = rsp0 /\\
          read R12 s = m /\\ read R13 s = word mlen /\\ read RDX s = word mlen /\\
          read (memory :> bytes(m,mlen)) s = M /\\
          read events s = e)
    (\\s. read RIP s = word (pc + %d) /\\ read RSP s = rsp0 /\\
          read (memory :> bytes(word_add rsp0 (word 384),64)) s =
            num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64) /\\
          (exists e2. read events s = APPEND e2 e /\\
             e2 = f_events m mlen rsp0 pc /\\
             memaccess_inbounds e2
              [m,mlen; word_add rsp0 (word 32),208; word_add rsp0 (word 384),64;
               word_sub (word_sub rsp0 (word 8)) (word 288),288;
               word_sub rsp0 (word 8),8;
               word(pc + rodata_mld_KeccakF_RoundConstants),192]
              [word_add rsp0 (word 32),208; word_add rsp0 (word 384),64;
               word_sub (word_sub rsp0 (word 8)) (word 288),288;
               word_sub rsp0 (word 8),8]))
    (MAYCHANGE [RIP; RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [R12; R13; %s] ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bytes(word_add rsp0 (word 32),208);
                memory :> bytes(word_add rsp0 (word 384),64);
                memory :> bytes(word_sub (word_sub rsp0 (word 8)) (word 288),288);
                memory :> bytes(word_sub rsp0 (word 8),8)])"
  (layout fn + 46) (layout fn + 699) sr);;

let SPONGE_REGION_VARS = [`m:int64`; `mlen:num`; `M:num`; `rsp0:int64`; `pc:num`];;

let SPONGE_REGION_TAC fn zero j1 tail fin =
  let exec = SPONGE_TAIL_EXEC fn in
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 zero) "H_ZERO" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 j1) "H_J1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 tail) "H_TAIL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 fin) "H_FIN" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(m:int64) (mlen:num) (rsp0:int64) (pc:num). f_ev_a m mlen rsp0 pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `m:int64`; `mlen:num`; `M:num`; `rsp0:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; NONOVERLAPPING_CLAUSES; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc exec "H_ZERO"
   [`rsp0:int64`; `pc:num`] SPONGE_REGION_VARS 1 THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc exec "H_J1"
   [`m:int64`; `mlen:num`; `M:num`; `rsp0:int64`; `pc:num`] SPONGE_REGION_VARS 2 THEN
  (*** the rest of the message after the blocks ***)
  SUBGOAL_THEN `M < 2 EXP (8 * mlen)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if concl th = `read (memory :> bytes (m,mlen)) s2 = M` then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND]; ALL_TAC] THEN
  SUBGOAL_THEN `mlen - 136 * (mlen DIV 136) < 136 /\ 136 * (mlen DIV 136) + (mlen - 136 * (mlen DIV 136)) <= mlen` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`mlen:num`; `136`] DIVISION) THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`m:int64`; `mlen:num`; `M:num`; `136 * (mlen DIV 136)`; `mlen - 136 * (mlen DIV 136)`; `s2:x86state`] READ_MEMORY_BYTES_SUB) THEN
  ANTS_TAC THENL [CONJ_TAC THENL [FIRST_ASSUM(fun th -> if concl th = `read (memory :> bytes (m,mlen)) s2 = M` then ACCEPT_TAC th else NO_TAC); FIRST_ASSUM ACCEPT_TAC]; DISCH_TAC] THEN
  SUBGOAL_THEN `nonoverlapping_modulo (2 EXP 64) (val (word_add (m:int64) (word (136 * (mlen DIV 136)))),mlen - 136 * (mlen DIV 136)) (val (word_add (rsp0:int64) (word 32)),200)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`m:int64`; `word_sub rsp0 (word 296):int64`; `mlen:num`; `744`; `136 * (mlen DIV 136)`; `mlen - 136 * (mlen DIV 136)`; `328`; `200`] SPONGE_NOV_SUB2) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST[FIRST_ASSUM ACCEPT_TAC; ARITH_TAC]; ALL_TAC] THEN
    REWRITE_TAC[WORD_RULE `word_add (word_sub (rsp0:int64) (word 296)) (word 328) = word_add rsp0 (word 32)`];
    ALL_TAC] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc exec "H_TAIL"
   [`word_add m (word (136 * (mlen DIV 136))):int64`; `mlen - 136 * (mlen DIV 136)`;
    `(M DIV 2 EXP (8 * (136 * (mlen DIV 136)))) MOD 2 EXP (8 * (mlen - 136 * (mlen DIV 136)))`;
    `mld_keccak_absorb_blocks 136 (word 0) M (mlen DIV 136)`; `rsp0:int64`; `pc:num`] SPONGE_REGION_VARS 3 THEN
  (*** the padding, the permutation and the copy ***)
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc exec "H_FIN"
   [`mlen - 136 * (mlen DIV 136)`;
    `word_xor (mld_keccak_absorb_blocks 136 (word 0) M (mlen DIV 136)) (word ((M DIV 2 EXP (8 * (136 * (mlen DIV 136)))) MOD 2 EXP (8 * (mlen - 136 * (mlen DIV 136))))):1600 word`;
    `rsp0:int64`; `pc:num`] SPONGE_REGION_VARS 4 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes (word_add rsp0 (word 384),64)) s4 = x`) (concl th) then SUBST1_TAC th else NO_TAC) THEN
    MATCH_MP_TAC SPONGE_REGION_LINK THEN FIRST_ASSUM ACCEPT_TAC;
    DISCHARGE_SAFETY_PROPERTY_SPINE_TAC];;

let PROVE_SPONGE_REGION fn sr zero j1 tail fin = prove(SPONGE_REGION_STMT fn sr, SPONGE_REGION_TAC fn zero j1 tail fin);;

(* ------------------------------------------------------------------------- *)
(* The region lemma of one of the six functions with all the lemmas that it  *)
(* uses; sr is R14 in the signing functions and RBX in the verification      *)
(* functions.                                                                *)
(* ------------------------------------------------------------------------- *)

let PROVE_SPONGE_FULL fn sr =
  let l1 = PROVE_SPONGE_L1 fn sr in
  let l2 = PROVE_SPONGE_L2 fn in
  let l4 = PROVE_SPONGE_L4 fn in
  let l5 = PROVE_SPONGE_L5 fn in
  let t5 = prove(SPONGE_T5_STMT fn, SPONGE_T5_TAC fn l2) in
  let t4 = prove(SPONGE_T4_STMT fn, SPONGE_T4_TAC fn l2 l5 t5) in
  let tail = prove(SPONGE_TAIL_STMT fn, SPONGE_TAIL_TAC fn l2 l4 l5 t4 t5) in
  let zero = PROVE_SPONGE_ZERO fn in
  let j1 = PROVE_SPONGE_J1 fn sr l1 in
  let fin = PROVE_SPONGE_FIN fn sr in
  PROVE_SPONGE_REGION fn sr zero j1 tail fin;;
