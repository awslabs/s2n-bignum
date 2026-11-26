(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The loops that XOR the last bytes of the message into the state of the    *)
(* SHAKE256 that clang 23 inlines into mldsa{44,65,87}_signature_pre_hash_   *)
(* shake256 and _verify_pre_hash_shake256, as lemmas from the head of the    *)
(* loop to its exit, which the proofs of those functions use as they use the *)
(* theorem for a subroutine (see inline_sponge_tail.ml for the arithmetic):  *)
(*                                                                           *)
(*  - loop5: 4 bytes per iteration, mov edx, [r12+rcx]; xor [rsp+rcx+0x20],  *)
(*    edx; add rcx, 4; cmp rax, rcx; jne, from byte 4 q0 to byte 4 q1 of the *)
(*    state;                                                                 *)
(*  - loop2: 1 byte per iteration (below);                                   *)
(*  - loop4: 32 bytes per iteration (below).                                 *)
(*                                                                           *)
(* The state is at rsp0 + 32 (200 bytes) and the data at R12. The invariant  *)
(* gives the bytes of the state one by one (facts for the bytes that an      *)
(* iteration does not write are kept over its store), and the lemma gives    *)
(* the state as the word S XORed with the data Tm up to the end.             *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sponge_loop1.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sponge_tail.ml";;

(* loop5 of the tail of the inlined SHAKE256: 4 bytes per iteration *)
let SPONGE_L5_EXEC fn = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [(layout (fn^"_loop5"), layout (fn^"_loop5_exit"))];;

let SPONGE_L5_STMT fn = parse_term(Printf.sprintf
 "exists f_events. forall e rsp0 mp q0 q1 (S:1600 word) Tm pc.
   q0 < q1 /\\ 4 * q1 <= 136 /\\
   aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   nonoverlapping (mp,4 * q1) (word_add rsp0 (word 32),200) /\\
   nonoverlapping (word pc,libmldsa_size) (word_add rsp0 (word 32),200)
   ==> ensures x86
     (\\s. bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
          read RIP s = word (pc + %s_loop5) /\\
          read RSP s = rsp0 /\\ read R12 s = mp /\\
          read RAX s = word (4 * q1) /\\ read RCX s = word (4 * q0) /\\
          read (memory :> bytes(mp,4 * q1)) s = Tm /\\
          read (memory :> wbytes (word_add rsp0 (word 32))) s =
            word_xor S (word (Tm MOD 2 EXP (8 * (4 * q0)))) /\\
          read events s = e)
     (\\s. read RIP s = word (pc + %s_loop5_exit) /\\
          read RSP s = rsp0 /\\ read R12 s = mp /\\
          read RAX s = word (4 * q1) /\\ read RCX s = word (4 * q1) /\\
          read (memory :> wbytes (word_add rsp0 (word 32))) s =
            word_xor S (word (Tm MOD 2 EXP (8 * (4 * q1)))) /\\
          (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 mp q0 q1 pc /\\
             memaccess_inbounds e2 [mp,4 * q1; word_add rsp0 (word 32),200]
                                   [word_add rsp0 (word 32),200]))
     (MAYCHANGE [RIP; RDX; RCX] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(word_add rsp0 (word 32),200)])"
  fn fn);;


let SPONGE_L5_INVBYTES = `\i s. read RSP s = rsp0 /\ read R12 s = mp /\
          read RAX s = word (4 * q1) /\ read RCX s = word (4 * (q0 + i)) /\
          read (memory :> bytes(mp,4 * q1)) s = Tm /\
          !j. j < 200
              ==> read (memory :> bytes8 (word_add rsp0 (word (j + 32)))) s =
                  word_subword
                   (word_xor (S:1600 word) (word (Tm MOD 2 EXP (8 * (4 * (q0 + i))))))
                   (8 * j,8)`;;

(*** The facts for the iteration: the bytes of the state and the chunk,
     in the forms of the addresses that the simulation uses ***)

let L5_RESTRICT_RULE p w th =
  let j,bod = dest_forall(concl th) in
  let pr,q = dest_imp bod in
  let jl = mk_comb(mk_comb(`(<):num->num->bool`,j),p) in
  let jh = mk_comb(mk_comb(`(<=):num->num->bool`,mk_binop `(+):num->num->num` p w),j) in
  let mk c = let pr' = mk_conj(pr,c) in GEN j (DISCH pr' (MP (SPEC j th) (CONJUNCT1(ASSUME pr')))) in
  [mk jl; mk jh];;

(* the state chunk fact in the form of the simulated address *)
let L5_STATE_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && free_in `bytes8` (concl th) then
      ASSUME_TAC(MATCH_MP SPONGE_WBYTES32_OF_ALL_BYTES th) THEN
      MAP_EVERY ASSUME_TAC (L5_RESTRICT_RULE `4 * (q0 + i)` `4` th)
    else failwith "L5_STATE_TAC") THEN
  FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> wbytes a) s0 = X`) (concl th) then
      ASSUME_TAC(REWRITE_RULE[SPONGE_BYTES32_ADDR; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]
        (MATCH_MP READ_MEMORY_BYTES32_OF_WBYTES (CONJ th (ASSUME `q0 + i < 50`))))
      else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes (mp,n)) s0 = Tm`) (concl th) then
      ASSUME_TAC(MATCH_MP READ_MEMORY_BYTES32_OF_NUM (CONJ th (ASSUME `4 * (q0 + i) + 4 <= 4 * q1`)))
      else NO_TAC);;

let L5_STATE_TAC2 =
  L5_STATE_TAC THEN
  SUBGOAL_THEN `read (memory :> bytes32 (word_add rsp0 (word (1 * 4 * (q0 + i) + 32)))) s0 =
      word_subword ((S:1600 word) ^^ word (Tm MOD 2 EXP (8 * 4 * (q0 + i)))) (32 * (q0 + i),32)` ASSUME_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC];;

let L5_MSG_TAC =
  SUBGOAL_THEN `read (memory :> bytes32 (word_add mp (word (1 * (4 * (q0 + i)))))) s0 =
      word ((Tm DIV 2 EXP (32 * (q0 + i))) MOD 2 EXP 32)` ASSUME_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC];;

(*** The test at the end of the loop ***)

let SPONGE_L5_TEST = prove
 (`!q0 q1 i. q0 < q1 /\ i < q1 - q0 /\ 4 * q1 <= 136
        ==> (~(val(word_sub (word (4 * q1)) (word_add (word (4 * (q0 + i))) (word 4)):int64) = 0)
             <=> i + 1 < q1 - q0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_sub (word (4 * q1)) (word_add (word (4 * (q0 + i))) (word 4)):int64 =
                word (4 * (q1 - (q0 + i + 1)))` SUBST1_TAC THENL
   [SUBGOAL_THEN `4 * (q0 + i + 1) <= 4 * q1` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM WORD_ADD; ARITH_RULE `4 * (q0 + i) + 4 = 4 * (q0 + i + 1)`] THEN
    ASM_SIMP_TAC[WORD_SUB2] THEN REWRITE_TAC[ARITH_RULE `4 * q1 - 4 * (q0 + i + 1) = 4 * (q1 - (q0 + i + 1))`];
    ALL_TAC] THEN
  SUBGOAL_THEN `4 * (q1 - (q0 + i + 1)) < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN ASM_ARITH_TAC);;

(*** The bytes of the state after the iteration ***)

let L5_BYTES_TAC =
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[ARITH_RULE `8 * 4 * (q0 + i + 1) = 8 * (4 * (q0 + i) + 4)`] THEN
  MP_TAC(SPECL [`S:1600 word`; `Tm:num`; `4 * (q0 + i)`; `4`; `j:num`] SPONGE_XOR_CHUNK_STEP) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`4 * (q0 + i) + 4 <= 4 * q1`; `4 * q1 <= 136`] THEN ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `?k. k < 4 /\ j = 4 * (q0 + i) + k` STRIP_ASSUME_TAC THENL
     [EXISTS_TAC `j - 4 * (q0 + i)` THEN
      UNDISCH_TAC `4 * (q0 + i) <= j /\ j < 4 * (q0 + i) + 4` THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [] `read (memory :> bytes32 (word_add rsp0 (word (1 * 4 * (q0 + i) + 32)))) s5 = v`) (concl th)
      then MP_TAC(MATCH_MP SPONGE_BYTES8_OF_CHUNK32 (CONJ th (ASSUME `k < 4`))) else NO_TAC) THEN
    SUBGOAL_THEN `word_add (word_add rsp0 (word (1 * 4 * (q0 + i) + 32))) (word k):int64 =
                  word_add rsp0 (word ((4 * (q0 + i) + k) + 32))` SUBST1_TAC THENL
     [CONV_TAC WORD_RULE; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPECL [`(S:1600 word) ^^ word (Tm MOD 2 EXP (8 * (4 * (q0 + i))))`; `Tm:num`; `q0 + i`; `k:num`] SPONGE_CHUNK_BYTE32) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[ARITH_RULE `8 * (4 * (q0 + i) + k) = 32 * (q0 + i) + 8 * k`];
    ASM_CASES_TAC `j < 4 * (q0 + i)` THENL
     [ASM_SIMP_TAC[];
      SUBGOAL_THEN `4 * (q0 + i) + 4 <= j` ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`~(4 * (q0 + i) <= j /\ j < 4 * (q0 + i) + 4)`; `~(j < 4 * (q0 + i))`] THEN ARITH_TAC;
        ASM_SIMP_TAC[]]]];;

let L5_FINAL_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; ARITH_RULE `4294967296 = 2 EXP 32`]) THEN
  MP_TAC(MATCH_MP SPONGE_L5_TEST (CONJ (ASSUME `q0 < q1`) (CONJ (ASSUME `i < q1 - q0`) (ASSUME `4 * q1 <= 136`)))) THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[];
    CONV_TAC WORD_RULE;
    L5_BYTES_TAC;
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let SPONGE_L5_BODY fn =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `q0 + i < 34` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `q0 + i < 50` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `4 * (q0 + i) + 4 <= 4 * q1` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FULL_INIT_TAC THEN VAL_INT64_TAC `4 * (q0 + i)` THEN
  L5_STATE_TAC2 THEN L5_MSG_TAC THEN
  X86_STEPS_TAC (SPONGE_L5_EXEC fn) (1--5) THEN
  L5_FINAL_TAC;;

let SPONGE_L5_TAC fn =
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (mp:int64) (q0:num) (q1:num) (pc:num).
      APPEND (f_ev_epil rsp0 mp q0 q1 pc)
       (APPEND (ENUMERATEL (q1 - q0) (\i. f_ev_loop rsp0 mp q0 q1 pc i)) (f_ev_prol rsp0 mp q0 q1 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `mp:int64`; `q0:num`; `q1:num`; `S:1600 word`; `Tm:num`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst (SPONGE_L5_EXEC fn)] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `q1 - q0` (parse_term (Printf.sprintf "pc + %s_loop5" fn))
   (parse_term (Printf.sprintf "pc + %s_loop5_exit" fn)) SPONGE_L5_INVBYTES THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> wbytes a) s0 = X`) (concl th) then ACCEPT_TAC(MATCH_MP SPONGE_ALL_BYTES_OF_WBYTES32 th) else NO_TAC);
      DISCHARGE_SAFETY_PROPERTY_TAC];
    SPONGE_L5_BODY fn;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN
    SUBGOAL_THEN `q0 + (q1 - q0) = q1` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `q0 < q1` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(fun th -> if is_forall(concl th) && free_in `bytes8` (concl th) then ACCEPT_TAC(MATCH_MP SPONGE_WBYTES32_OF_ALL_BYTES th) else NO_TAC);
      DISCHARGE_SAFETY_PROPERTY_TAC]];;

let PROVE_SPONGE_L5 fn = prove(SPONGE_L5_STMT fn, SPONGE_L5_TAC fn);;

(* ------------------------------------------------------------------------- *)
(* loop2: one byte per iteration, movzx esi, BYTE PTR [r12+rcx*1]; xor       *)
(* BYTE PTR [rsp+rcx*1+0x20], sil; inc rcx; dec rdx; jne, from byte i0 of    *)
(* the state, c bytes.                                                       *)
(* ------------------------------------------------------------------------- *)

let SPONGE_L2_EXEC fn = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [(layout (fn^"_loop2"), layout (fn^"_loop2_exit"))];;

let SPONGE_L2_STMT fn = parse_term(Printf.sprintf
 "exists f_events. forall e rsp0 mp i0 c (S:1600 word) Tm pc.
   0 < c /\\ i0 + c <= 136 /\\
   aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   nonoverlapping (mp,i0 + c) (word_add rsp0 (word 32),200) /\\
   nonoverlapping (word pc,libmldsa_size) (word_add rsp0 (word 32),200)
   ==> ensures x86
     (\\s. bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
          read RIP s = word (pc + %s_loop2) /\\
          read RSP s = rsp0 /\\ read R12 s = mp /\\
          read RCX s = word i0 /\\ read RDX s = word c /\\
          read (memory :> bytes(mp,i0 + c)) s = Tm /\\
          read (memory :> wbytes (word_add rsp0 (word 32))) s =
            word_xor S (word (Tm MOD 2 EXP (8 * i0))) /\\
          read events s = e)
     (\\s. read RIP s = word (pc + %s_loop2_exit) /\\
          read RSP s = rsp0 /\\ read R12 s = mp /\\
          read RCX s = word (i0 + c) /\\ read RDX s = word 0 /\\
          read (memory :> wbytes (word_add rsp0 (word 32))) s =
            word_xor S (word (Tm MOD 2 EXP (8 * (i0 + c)))) /\\
          (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 mp i0 c pc /\\
             memaccess_inbounds e2 [mp,i0 + c; word_add rsp0 (word 32),200]
                                   [word_add rsp0 (word 32),200]))
     (MAYCHANGE [RIP; RSI; RCX; RDX] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(word_add rsp0 (word 32),200)])"
  fn fn);;

let SPONGE_L2_INVBYTES = `\i s. read RSP s = rsp0 /\ read R12 s = mp /\
          read RCX s = word (i0 + i) /\ read RDX s = word (c - i) /\
          read (memory :> bytes(mp,i0 + c)) s = Tm /\
          !j. j < 200
              ==> read (memory :> bytes8 (word_add rsp0 (word (j + 32)))) s =
                  word_subword
                   (word_xor (S:1600 word) (word (Tm MOD 2 EXP (8 * (i0 + i)))))
                   (8 * j,8)`;;

(*** The facts for an iteration, at byte p = i0 + i ***)

let L2_RESTRICT_RULE p th =
  let j,bod = dest_forall(concl th) in
  let pr,q = dest_imp bod in
  let mk c = let pr' = mk_conj(pr,c) in GEN j (DISCH pr' (MP (SPEC j th) (CONJUNCT1(ASSUME pr')))) in
  [mk (mk_comb(mk_comb(`(<):num->num->bool`,j),p));
   mk (mk_comb(mk_comb(`(<=):num->num->bool`,mk_binop `(+):num->num->num` p `1`),j))];;

let L2_STATE_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && free_in `bytes8` (concl th) then
      MAP_EVERY ASSUME_TAC (L2_RESTRICT_RULE `i0 + i` th) THEN
      ASSUME_TAC(MP (SPEC `i0 + i` th) (ASSUME `i0 + i < 200`))
    else failwith "L2_STATE_TAC") THEN
  FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes (mp,n)) s0 = Tm`) (concl th) then
      ASSUME_TAC(MATCH_MP READ_MEMORY_BYTES8_OF_NUM (CONJ th (ASSUME `i0 + i < i0 + c`)))
      else NO_TAC);;

let L2_FORMS_TAC =
  SUBGOAL_THEN `read (memory :> bytes8 (word_add rsp0 (word (1 * (i0 + i) + 32)))) s0 =
      word_subword ((S:1600 word) ^^ word (Tm MOD 2 EXP (8 * (i0 + i)))) (8 * (i0 + i),8)` ASSUME_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes8 (word_add mp (word (1 * (i0 + i))))) s0 =
      word ((Tm DIV 2 EXP (8 * (i0 + i))) MOD 256)` ASSUME_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC];;

let SPONGE_L2_TEST = prove
 (`!c i. i < c /\ c < 2 EXP 64
        ==> (~(val(word_sub (word (c - i)) (word 1):int64) = 0) <=> i + 1 < c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_sub (word (c - i)) (word 1):int64 = word (c - (i + 1))` SUBST1_TAC THENL
   [SUBGOAL_THEN `1 <= c - i` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[WORD_SUB2] THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c - (i + 1) < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN ASM_ARITH_TAC);;


let SPONGE_L2_VALZX = prove
 (`!Tm k. val(word_zx(word_zx(word ((Tm DIV 2 EXP k) MOD 256):byte):int32):int64) =
          (Tm DIV 2 EXP k) MOD 256`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; MOD_MOD_EXP_MIN] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let SPONGE_L2_BYTES_TAC =
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[ARITH_RULE `i0 + (i + 1) = (i0 + i) + 1`] THEN
  MP_TAC(SPECL [`S:1600 word`; `Tm:num`; `i0 + i`; `j:num`] SPONGE_XOR_BYTE_STEP) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`i0 + c <= 136`; `i < c`] THEN ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(fun th -> if concl th = `j = i0 + i` then SUBST_ALL_TAC th else NO_TAC) THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [] `read (memory :> bytes8 (word_add rsp0 (word (1 * (i0 + i) + 32)))) s5 = v`) (concl th)
      then ACCEPT_TAC(REWRITE_RULE[MULT_CLAUSES] th) else NO_TAC);
    ASM_CASES_TAC `j < i0 + i` THENL
     [FIRST_X_ASSUM(fun th -> if is_forall(concl th) && free_in `bytes8` (concl th) && not(free_in `(<=):num->num->bool` (concl th)) && free_in `s5:x86state` (concl th)
              then ACCEPT_TAC(MP (SPEC `j:num` th) (CONJ (ASSUME `j < 200`) (ASSUME `j < i0 + i`))) else NO_TAC);
      SUBGOAL_THEN `(i0 + i) + 1 <= j` ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`~(j = i0 + i)`; `~(j < i0 + i)`] THEN ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(fun th -> if is_forall(concl th) && free_in `bytes8` (concl th) && can (find_term (fun t -> try fst(dest_const t) = "<=" with _ -> false)) (concl th) && free_in `s5:x86state` (concl th)
              then ACCEPT_TAC(MP (SPEC `j:num` th) (CONJ (ASSUME `j < 200`) (ASSUME `(i0 + i) + 1 <= j`))) else NO_TAC)]];;

let SPONGE_L2_FINAL =
  RULE_ASSUM_TAC(REWRITE_RULE[SPONGE_L2_VALZX; MOD_MOD_REFL]) THEN
  MP_TAC(MATCH_MP SPONGE_L2_TEST (CONJ (ASSUME `i < c`) (ASSUME `c < 2 EXP 64`))) THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[];
    CONV_TAC WORD_RULE;
    SUBGOAL_THEN `word_sub (word (c - i)) (word 1):int64 = word (c - (i + 1))` SUBST1_TAC THENL
     [SUBGOAL_THEN `1 <= c - i` ASSUME_TAC THENL [UNDISCH_TAC `i < c` THEN ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[WORD_SUB2] THEN AP_TERM_TAC THEN ARITH_TAC;
      REWRITE_TAC[]];
    SPONGE_L2_BYTES_TAC;
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let SPONGE_L2_BODY fn =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `i0 + i < 200` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `i0 + i < i0 + c` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c < 2 EXP 64` ASSUME_TAC THENL [UNDISCH_TAC `i0 + c <= 136` THEN ARITH_TAC; ALL_TAC] THEN
  FULL_INIT_TAC THEN VAL_INT64_TAC `i0 + i` THEN L2_STATE_TAC THEN L2_FORMS_TAC THEN
  X86_STEPS_TAC (SPONGE_L2_EXEC fn) (1--5) THEN
  SPONGE_L2_FINAL;;

let SPONGE_L2_TAC fn =
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (mp:int64) (i0:num) (c:num) (pc:num).
      APPEND (f_ev_epil rsp0 mp i0 c pc)
       (APPEND (ENUMERATEL c (\i. f_ev_loop rsp0 mp i0 c pc i)) (f_ev_prol rsp0 mp i0 c pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `mp:int64`; `i0:num`; `c:num`; `S:1600 word`; `Tm:num`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst (SPONGE_L2_EXEC fn)] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `c:num` (parse_term (Printf.sprintf "pc + %s_loop2" fn))
   (parse_term (Printf.sprintf "pc + %s_loop2_exit" fn)) SPONGE_L2_INVBYTES THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; SUB_0] THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> wbytes a) s0 = X`) (concl th) then ACCEPT_TAC(MATCH_MP SPONGE_ALL_BYTES_OF_WBYTES32 th) else NO_TAC);
      DISCHARGE_SAFETY_PROPERTY_TAC];
    SPONGE_L2_BODY fn;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[SUB_REFL] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(fun th -> if is_forall(concl th) && free_in `bytes8` (concl th) then ACCEPT_TAC(MATCH_MP SPONGE_WBYTES32_OF_ALL_BYTES th) else NO_TAC);
      DISCHARGE_SAFETY_PROPERTY_TAC]];;

let PROVE_SPONGE_L2 fn = prove(SPONGE_L2_STMT fn, SPONGE_L2_TAC fn);;

(* ------------------------------------------------------------------------- *)
(* loop4: 32 bytes per iteration, two chunks of 16 bytes each, with SSE      *)
(* instructions, from the start of the state to byte 32 q.                   *)
(* ------------------------------------------------------------------------- *)

let SPONGE_L4_EXEC fn = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [(layout (fn^"_loop4"), layout (fn^"_loop4_exit"))];;

let SPONGE_L4_STMT fn = parse_term(Printf.sprintf
 "exists f_events. forall e rsp0 mp q (S:1600 word) Tm pc.
   0 < q /\\ 32 * q <= 136 /\\ aligned 16 rsp0 /\\
   aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   nonoverlapping (mp,32 * q) (word_add rsp0 (word 32),200) /\\
   nonoverlapping (word pc,libmldsa_size) (word_add rsp0 (word 32),200)
   ==> ensures x86
     (\\s. bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
          read RIP s = word (pc + %s_loop4) /\\
          read RSP s = rsp0 /\\ read R12 s = mp /\\
          read RAX s = word (32 * q) /\\ read RCX s = word 0 /\\
          read (memory :> bytes(mp,32 * q)) s = Tm /\\
          read (memory :> wbytes (word_add rsp0 (word 32))) s = S /\\
          read events s = e)
     (\\s. read RIP s = word (pc + %s_loop4_exit) /\\
          read RSP s = rsp0 /\\ read R12 s = mp /\\
          read RAX s = word (32 * q) /\\ read RCX s = word (32 * q) /\\
          read (memory :> wbytes (word_add rsp0 (word 32))) s =
            word_xor S (word Tm) /\\
          (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 mp q pc /\\
             memaccess_inbounds e2 [mp,32 * q; word_add rsp0 (word 32),200]
                                   [word_add rsp0 (word 32),200]))
     (MAYCHANGE [RIP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(word_add rsp0 (word 32),200)])"
  fn fn);;

let SPONGE_L4_INVBYTES = `\i s. read RSP s = rsp0 /\ read R12 s = mp /\
          read RAX s = word (32 * q) /\ read RCX s = word (32 * i) /\
          read (memory :> bytes(mp,32 * q)) s = Tm /\
          !j. j < 200
              ==> read (memory :> bytes8 (word_add rsp0 (word (j + 32)))) s =
                  word_subword
                   (word_xor (S:1600 word) (word (Tm MOD 2 EXP (8 * (32 * i)))))
                   (8 * j,8)`;;

(*** A fact about a chunk in memory, with its address in the form that the
     simulation uses: the equation of the addresses is proved by WORD_RULE ***)

let SPONGE_RETARGET th (old_a:term) (new_a:term) =
  let eq = prove(mk_eq(old_a,new_a),CONV_TAC WORD_RULE) in
  REWRITE_RULE[eq] th;;

let L4_STATE_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && free_in `bytes8` (concl th) then
      ASSUME_TAC(MATCH_MP SPONGE_WBYTES32_OF_ALL_BYTES th) THEN
      MAP_EVERY ASSUME_TAC (L5_RESTRICT_RULE `32 * i` `32` th)
    else failwith "L4_STATE_TAC") THEN
  FIRST_ASSUM(fun wth ->
    if can (term_match [] `read (memory :> wbytes a) s0 = X`) (concl wth) then
      let c0 = MATCH_MP READ_MEMORY_BYTES128_OF_WBYTES (CONJ wth (ASSUME `2 * i < 12`))
      and c1 = MATCH_MP READ_MEMORY_BYTES128_OF_WBYTES (CONJ wth (ASSUME `2 * i + 1 < 12`)) in
      let c0' = SPONGE_RETARGET (REWRITE_RULE[SPONGE_BYTES32_ADDR] c0)
        `word_add rsp0 (word (16 * (2 * i) + 32)):int64`
        `word_add rsp0 (word (1 * (32 * i) + 32)):int64`
      and c1' = SPONGE_RETARGET (REWRITE_RULE[SPONGE_BYTES32_ADDR] c1)
        `word_add rsp0 (word (16 * (2 * i + 1) + 32)):int64`
        `word_add rsp0 (word (1 * (32 * i) + 48)):int64` in
      ASSUME_TAC c0' THEN ASSUME_TAC c1'
    else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes (mp,n)) s0 = Tm`) (concl th) then
    let m0 = MATCH_MP READ_MEMORY_BYTES128_OF_NUM (CONJ th (ASSUME `16 * (2 * i) + 16 <= 32 * q`))
    and m1 = MATCH_MP READ_MEMORY_BYTES128_OF_NUM (CONJ th (ASSUME `16 * (2 * i + 1) + 16 <= 32 * q`)) in
    let m0' = SPONGE_RETARGET m0 `word_add mp (word (16 * (2 * i))):int64` `word_add mp (word (1 * (32 * i))):int64`
    and m1' = SPONGE_RETARGET m1 `word_add mp (word (16 * (2 * i + 1))):int64` `word_add mp (word (1 * (32 * i) + 16)):int64` in
    ASSUME_TAC m0' THEN ASSUME_TAC m1'
    else NO_TAC);;

(*** movups xmm0, [m]; xorps xmm0, [s]; the low 128 bits of the result ***)

let SPONGE_XMM_XOR = prove
 (`!(y:256 word) (m:128 word) (c:128 word).
     word_subword (word_join (word_subword (word_join (word_subword y (128,128)) m:256 word) (128,128):128 word)
                             (word_subword (word_join (word_subword y (128,128)) m:256 word) (0,128) ^^ c)
                   :256 word) (0,128):128 word = c ^^ m`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

let SPONGE_L4_TEST = prove
 (`!q i. i < q /\ 32 * q <= 136
        ==> (~(val(word_sub (word (32 * q)) (word_add (word (32 * i)) (word 32)):int64) = 0)
             <=> i + 1 < q)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_sub (word (32 * q)) (word_add (word (32 * i)) (word 32)):int64 =
                word (32 * (q - (i + 1)))` SUBST1_TAC THENL
   [SUBGOAL_THEN `32 * (i + 1) <= 32 * q` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM WORD_ADD; ARITH_RULE `32 * i + 32 = 32 * (i + 1)`] THEN
    ASM_SIMP_TAC[WORD_SUB2] THEN REWRITE_TAC[ARITH_RULE `32 * q - 32 * (i + 1) = 32 * (q - (i + 1))`];
    ALL_TAC] THEN
  SUBGOAL_THEN `32 * (q - (i + 1)) < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN ASM_ARITH_TAC);;

let L4_ALIGNED_LEMMA k = prove(parse_term(Printf.sprintf "aligned 16 (word (1 * (32 * i) + %d):int64)" k),
          REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
          CONJ_TAC THENL [CONV_TAC NUM_DIVIDES_CONV; ALL_TAC] THEN
          REWRITE_TAC[divides] THEN EXISTS_TAC (parse_term(Printf.sprintf "2 * i + %d" (k/16))) THEN ARITH_TAC);;
let L4_ALIGN_TAC =
  FIRST_ASSUM(fun ra -> if concl ra = `aligned 16 (rsp0:int64)` then
    MAP_EVERY (fun k ->
      ASSUME_TAC(MATCH_MP ALIGNED_WORD_ADD (CONJ ra (L4_ALIGNED_LEMMA k))))
     [32;48]
    else NO_TAC);;

let L4_INRANGE_TAC =
  SUBGOAL_THEN `?t. t < 32 /\ j = 32 * i + t` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `j - 32 * i` THEN UNDISCH_TAC `32 * i <= j /\ j < 32 * i + 32` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if concl th = `j = 32 * i + t` then SUBST_ALL_TAC th else NO_TAC) THEN
  ASM_CASES_TAC `t < 16` THENL
   [FIRST_ASSUM(fun th ->
      if can (term_match [] `read (memory :> bytes128 (word_add rsp0 (word (1 * 32 * i + 32)))) s9 = v`) (concl th)
      then MP_TAC(MATCH_MP SPONGE_BYTES8_OF_CHUNK128 (CONJ th (ASSUME `t < 16`))) else NO_TAC) THEN
    SUBGOAL_THEN `word_add (word_add rsp0 (word (1 * 32 * i + 32))) (word t):int64 =
                  word_add rsp0 (word ((32 * i + t) + 32))` SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPECL [`(S:1600 word) ^^ word (Tm MOD 2 EXP (8 * 32 * i))`; `Tm:num`; `2 * i`; `t:num`] SPONGE_CHUNK_BYTE128) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[ARITH_RULE `8 * (32 * i + t) = 128 * (2 * i) + 8 * t`];
    SUBGOAL_THEN `?k. k < 16 /\ t = 16 + k` STRIP_ASSUME_TAC THENL
     [EXISTS_TAC `t - 16` THEN MAP_EVERY UNDISCH_TAC [`~(t < 16)`; `t < 32`] THEN ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if concl th = `t = 16 + k` then SUBST_ALL_TAC th else NO_TAC) THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [] `read (memory :> bytes128 (word_add rsp0 (word (1 * 32 * i + 48)))) s9 = v`) (concl th)
      then MP_TAC(MATCH_MP SPONGE_BYTES8_OF_CHUNK128 (CONJ th (ASSUME `k < 16`))) else NO_TAC) THEN
    SUBGOAL_THEN `word_add (word_add rsp0 (word (1 * 32 * i + 48))) (word k):int64 =
                  word_add rsp0 (word ((32 * i + (16 + k)) + 32))` SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPECL [`(S:1600 word) ^^ word (Tm MOD 2 EXP (8 * 32 * i))`; `Tm:num`; `2 * i + 1`; `k:num`] SPONGE_CHUNK_BYTE128) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[ARITH_RULE `8 * (32 * i + 16 + k) = 128 * (2 * i + 1) + 8 * k`]];;

let L4_OUT_TAC =
  ASM_CASES_TAC `j < 32 * i` THENL
   [FIRST_X_ASSUM(fun th -> if is_forall(concl th) && free_in `bytes8` (concl th) && not(free_in `(<=):num->num->bool` (concl th)) && free_in `s9:x86state` (concl th)
              then ACCEPT_TAC(MP (SPEC `j:num` th) (CONJ (ASSUME `j < 200`) (ASSUME `j < 32 * i`))) else NO_TAC);
    SUBGOAL_THEN `(32 * i) + 32 <= j` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`~(32 * i <= j /\ j < 32 * i + 32)`; `~(j < 32 * i)`] THEN ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) && free_in `bytes8` (concl th) && can (find_term (fun t -> try fst(dest_const t) = "<=" with _ -> false)) (concl th) && free_in `s9:x86state` (concl th)
              then ACCEPT_TAC(MP (SPEC `j:num` th) (CONJ (ASSUME `j < 200`) (ASSUME `(32 * i) + 32 <= j`))) else NO_TAC)];;

let L4_BYTES_TAC =
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[ARITH_RULE `8 * 32 * (i + 1) = 8 * (32 * i + 32)`] THEN
  MP_TAC(SPECL [`S:1600 word`; `Tm:num`; `32 * i`; `32`; `j:num`] SPONGE_XOR_CHUNK_STEP) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`32 * i + 32 <= 32 * q`; `32 * q <= 136`] THEN ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  COND_CASES_TAC THENL [L4_INRANGE_TAC; L4_OUT_TAC];;

let L4_FINAL =
  RULE_ASSUM_TAC(REWRITE_RULE[SPONGE_XMM_XOR; ARITH_RULE `340282366920938463463374607431768211456 = 2 EXP 128`]) THEN
  MP_TAC(MATCH_MP SPONGE_L4_TEST (CONJ (ASSUME `i < q`) (ASSUME `32 * q <= 136`))) THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[];
    CONV_TAC WORD_RULE;
    L4_BYTES_TAC;
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let SPONGE_L4_BODY fn =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `i < 5` ASSUME_TAC THENL [UNDISCH_TAC `i < q` THEN UNDISCH_TAC `32 * q <= 136` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `32 * i + 32 <= 32 * q` ASSUME_TAC THENL [UNDISCH_TAC `i < q` THEN ARITH_TAC; ALL_TAC] THEN
  FULL_INIT_TAC THEN VAL_INT64_TAC `32 * i` THEN
  YMM_GHOST_TAC `s0:x86state` ["YMM0","y0"; "YMM1","y1"] THEN
  SUBGOAL_THEN `2 * i < 12 /\ 2 * i + 1 < 12 /\ 16 * (2 * i) + 16 <= 32 * q /\ 16 * (2 * i + 1) + 16 <= 32 * q` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`i < 5`; `32 * i + 32 <= 32 * q`] THEN ARITH_TAC; ALL_TAC] THEN
  L4_STATE_TAC THEN L4_ALIGN_TAC THEN
  X86_STEPS_TAC (SPONGE_L4_EXEC fn) (1--9) THEN
  L4_FINAL;;

let SPONGE_L4_TAC fn =
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (mp:int64) (q:num) (pc:num).
      APPEND (f_ev_epil rsp0 mp q pc)
       (APPEND (ENUMERATEL q (\i. f_ev_loop rsp0 mp q pc i)) (f_ev_prol rsp0 mp q pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `mp:int64`; `q:num`; `S:1600 word`; `Tm:num`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; NONOVERLAPPING_CLAUSES; ALL; fst (SPONGE_L4_EXEC fn)] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `q:num` (parse_term (Printf.sprintf "pc + %s_loop4" fn))
   (parse_term (Printf.sprintf "pc + %s_loop4_exit" fn)) SPONGE_L4_INVBYTES THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; EXP; MOD_1; WORD_XOR_0] THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> wbytes a) s0 = X`) (concl th) then ACCEPT_TAC(MATCH_MP SPONGE_ALL_BYTES_OF_WBYTES32 th) else NO_TAC);
      DISCHARGE_SAFETY_PROPERTY_TAC];
    SPONGE_L4_BODY fn;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN
    SUBGOAL_THEN `Tm MOD 2 EXP (8 * (32 * q)) = Tm` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC MOD_LT THEN
      FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes (mp,n)) s0 = Tm`) (concl th)
                  then SUBST1_TAC(SYM th) else NO_TAC) THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(fun th -> if is_forall(concl th) && free_in `bytes8` (concl th) then ACCEPT_TAC(MATCH_MP SPONGE_WBYTES32_OF_ALL_BYTES th) else NO_TAC);
      DISCHARGE_SAFETY_PROPERTY_TAC]];;

let PROVE_SPONGE_L4 fn = prove(SPONGE_L4_STMT fn, SPONGE_L4_TAC fn);;
