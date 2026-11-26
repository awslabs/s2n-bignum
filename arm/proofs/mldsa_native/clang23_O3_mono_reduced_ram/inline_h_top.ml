(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The composition of the region lemmas of inline_h.ml into the proofs of    *)
(* mld_H44, mld_H65 and mld_H87: the prologue (with the zeroing of the       *)
(* state), the three absorbs, the padding, the squeezing (a loop with        *)
(* memcpy in mld_H44/65, one permutation and a copy of 64 bytes in mld_H87), *)
(* the zeroing of the state and the epilogue with the stack guard check.     *)
(* The absorbs compose as in the gcc proof (MLD_SHAKE256_ABSORB_APPEND and   *)
(* MLD_SHAKE256_ABSORB_APPEND3 of common/fips204/properties/                 *)
(* mldsa_native_hash.ml).                                                    *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_h.ml";;

type hlem = { la1 : thm; la2 : thm; la3 : thm; lfin : thm; lsq : thm option };;

let H_TIMED name f =
  let t0 = Unix.gettimeofday() in
  let th = f () in
  Printf.printf "H_TIME %s %.1f\n%!" name (Unix.gettimeofday() -. t0); th;;

let H_PROVE_ALL h =
  let tm n f = H_TIMED (h.hf ^ " " ^ n) f in
  let t1 = tm "T1" (fun () -> H_PROVE_T1 h) in
  let l1 = tm "L1" (fun () -> H_PROVE_L1 h) in
  let a1 = tm "A1" (fun () -> H_PROVE_A1 h l1 t1) in
  let ab t =
    let st = string_of_int t in
    let tvb = tm ("TVB" ^ st) (fun () -> H_PROVE_TVB h t) in
    let tvv = tm ("TVV" ^ st) (fun () -> H_PROVE_TVV h t) in
    let f = tm ("F" ^ st) (fun () -> H_PROVE_F h t) in
    let p = tm ("P" ^ st) (fun () -> H_PROVE_P h t f) in
    tm ("A" ^ st) (fun () -> H_PROVE_A h t p tvb tvv) in
  let a2 = ab 2 in
  let a3 = ab 3 in
  let fin = tm "FIN" (fun () -> H_PROVE_FIN h) in
  let sq = if h.hf = "mld_H87" then None
           else Some(tm "SQ" (fun () -> H_PROVE_SQ h)) in
  { la1 = a1; la2 = a2; la3 = a3; lfin = fin; lsq = sq };;

(*** The bound of a length from the nonoverlapping of its buffer with the
     k bytes of the frame at stackpointer, and its value as a word ***)

let H_LEN_TAC k a l =
  SUBGOAL_THEN (subst [l,`l:num`] `l < 2 EXP 64 /\ val(word l:int64) = l`)
    STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN (subst [k,`k:num`; l,`l:num`] `k + l <= 18446744073709551616`)
      ASSUME_TAC THENL
     [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
      MAP_EVERY EXISTS_TAC
       [`val(stackpointer:int64)`; mk_comb(`val:int64->num`,a)] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC];;

(*** The safety discharge at the end, with the events split at APPENDs ***)

let H_SAFETY_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  (CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]) THEN
  REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN
  REPEAT CONJ_TAC THEN DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

(* ------------------------------------------------------------------------- *)
(* The top level of mld_H44/65. After the offset of the stack pointer, the   *)
(* frame is stackpointer .. stackpointer + 544, the stack of the permutation *)
(* the first 240 bytes, the state at sp = stackpointer + 240, the canary at  *)
(* sp + 216 and the saved registers at sp + 224.                             *)
(* ------------------------------------------------------------------------- *)

let H_TOP_VARS =
  [`out:int64`; `outlen:num`; `in1:int64`; `in1len:num`; `in2:int64`;
   `in2len:num`; `in3:int64`; `in3len:num`; `guard:int64`; `mc:int64`;
   `pc:num`; `stackpointer:int64`; `returnaddress:int64`];;

let H_TOP_CALL exec name ilist n =
  H_FULL_CALL_TAC exec name ilist H_TOP_VARS n;;

let H_SP = `word_add stackpointer (word 240):int64`;;

(*** The 8 bytes of the state above the 192 that the stores of 32 bytes cover:
     bytes 192..199 from the store of 16 bytes at sp + 188, before the store
     at sp + 160 overwrites 188..191 ***)

let H_TOP_PIECE_TAC sname =
  let s = mk_var(sname,`:armstate`) in
  let a = `word_add stackpointer (word 428):int64` in
  MP_TAC(SPECL [a; `word 0:int128`; s] READ_MEMORY_BYTES_OF_WORD128) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_0] THEN DISCH_TAC THEN
  MP_TAC(SPECL [a; `16`; `0`; `4`; `8`; s] SPONGE2_BYTES_SUB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DIV_0; MOD_0] THEN
  CONV_TAC(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC DEPTH_CONV NUM_ADD_CONV) THEN
  DISCH_TAC;;

let H_TOP_ZERO_TAC sname =
  let s = mk_var(sname,`:armstate`) in
  MP_TAC(SPECL [H_SP; s] SPONGE3_ZERO_STATE) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC];;

let H_TOP_BODY_TAC h exec =
  let mc = mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc in
  SUBGOAL_THEN `in1len MOD 136 < 136 /\ (in1len + in2len) MOD 136 < 136 /\
                (in1len + in2len + in3len) MOD 136 < 136`
   STRIP_ASSUME_TAC THENL [REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  ARM_STEPS_TAC exec (1--7) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC exec (8--21) THEN
  H_TOP_PIECE_TAC "s21" THEN
  ARM_STEPS_TAC exec (22--27) THEN
  H_TOP_ZERO_TAC "s27" THEN
  H_TOP_CALL exec "H_A1"
   [`in1:int64`; `in1len:num`; `M1:num`; H_SP; `pc:num`] 28 THEN
  H_TOP_CALL exec "H_A2"
   [`in2:int64`; `in2len:num`; `M2:num`;
    `FST(mld_keccak_absorb 136 (word 0) 0 in1len M1)`; `in1len MOD 136`;
    H_SP; `pc:num`] 29 THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPECL [`in1len:num`; `in2len:num`; `M1:num`; `M2:num`] MLD_SHAKE256_ABSORB_APPEND)
       (ASSUME `M1 < 2 EXP (8 * in1len)`);
    MLD_KECCAK_POS_ADD]) THEN
  H_TOP_CALL exec "H_A3"
   [`in3:int64`; `in3len:num`; `M3:num`;
    `FST(mld_keccak_absorb 136 (word 0) 0 (in1len + in2len) (M1 + 2 EXP (8 * in1len) * M2))`;
    `(in1len + in2len) MOD 136`; H_SP; `pc:num`] 30 THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPECL [`in1len:num`; `in2len:num`; `in3len:num`;
               `M1:num`; `M2:num`; `M3:num`] MLD_SHAKE256_ABSORB_APPEND3)
       (CONJ (ASSUME `M1 < 2 EXP (8 * in1len)`) (ASSUME `M2 < 2 EXP (8 * in2len)`));
    MLD_KECCAK_POS_ADD; GSYM ADD_ASSOC]) THEN
  H_TOP_CALL exec "H_FIN"
   [`FST(mld_keccak_absorb 136 (word 0) 0 (in1len + in2len + in3len)
          (M1 + 2 EXP (8 * in1len) * (M2 + 2 EXP (8 * in2len) * M3)))`;
    `(in1len + in2len + in3len) MOD 136`; H_SP; `pc:num`] 31 THEN
  H_TOP_CALL exec "H_SQ"
   [`out:int64`; `outlen:num`;
    `mld_keccak_finalize 136 31
       (FST(mld_keccak_absorb 136 (word 0) 0 (in1len + in2len + in3len)
             (M1 + 2 EXP (8 * in1len) * (M2 + 2 EXP (8 * in2len) * M3))))
       ((in1len + in2len + in3len) MOD 136)`; H_SP; `pc:num`] 32 THEN
  ARM_STEPS_TAC exec (33--49) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC exec (50--76) THEN
  REWRITE_TAC[mld_shake256_byte; mld_shake256_state; MLD_KECCAK_ABSORB_SND; ADD_CLAUSES] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FIRST [REWRITE_TAC[] THEN NO_TAC; ASM_REWRITE_TAC[] THEN NO_TAC; H_SAFETY_TAC];;

let H_TOP_TAC h exec lem =
  let sq = match lem.lsq with Some th -> th | None -> failwith "H_TOP_TAC: no SQ" in
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
      (MP (SPECL [`mc:int64`;`ea:int64`;`el:num`;`ev:num`] sq) th) "H_SQ") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC lem.la1 "H_A1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC lem.la2 "H_A2" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC lem.la3 "H_A3" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC lem.lfin "H_FIN" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(out:int64) (outlen:num) (in1:int64) (in1len:num) (in2:int64) (in2len:num)
     (in3:int64) (in3len:num) (guard:int64) (mc:int64) (pc:num)
     (stackpointer:int64) (returnaddress:int64).
      f_ev_top out outlen in1 in1len in2 in2len in3 in3len guard mc pc
               stackpointer returnaddress:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL; ALLPAIRS;
              PAIRWISE; NONOVERLAPPING_CLAUSES; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64) /\
                aligned 16 (word_add stackpointer (word 240):int64)`
   STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 544):int64)` THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY (fun g -> REWRITE_TAC[SPECL [`pc:num`; g] WORD_ADD] THEN
                      RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; g] WORD_ADD]))
   [`got_stack_chk_guard:num`; `got_memcpy:num`] THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
                        (mk_const("X"^string_of_int n,[]))) ((19--26) @ [29]) THEN
  FULL_INIT_TAC THEN
  MLD_H_BOUND_TAC `in1:int64` THEN MLD_H_BOUND_TAC `in2:int64` THEN
  MLD_H_BOUND_TAC `in3:int64` THEN
  H_LEN_TAC `544` `in1:int64` `in1len:num` THEN
  H_LEN_TAC `544` `in2:int64` `in2len:num` THEN
  H_LEN_TAC `544` `in3:int64` `in3len:num` THEN
  H_LEN_TAC `544` `out:int64` `outlen:num` THEN
  H_TOP_BODY_TAC h exec;;

(* ------------------------------------------------------------------------- *)
(* The top level of mld_H87: the frame is stackpointer .. stackpointer + 560 *)
(* (as the statement allows), the state at stackpointer + 256. The padding   *)
(* ends at the call of the permutation; then the code copies the first 64    *)
(* bytes of the state to out (4 loads and stores of 16 bytes) and zeroes the *)
(* state.                                                                    *)
(* ------------------------------------------------------------------------- *)

let H_SP87 = `word_add stackpointer (word 256):int64`;;

let H_TOP87_VARS =
  [`out:int64`; `in1:int64`; `in1len:num`; `in2:int64`; `in2len:num`;
   `in3:int64`; `in3len:num`; `guard:int64`; `pc:num`; `stackpointer:int64`;
   `returnaddress:int64`];;

let H_TOP87_PIECE_TAC sname =
  let s = mk_var(sname,`:armstate`) in
  let a = `word_add stackpointer (word 444):int64` in
  MP_TAC(SPECL [a; `word 0:int128`; s] READ_MEMORY_BYTES_OF_WORD128) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_0] THEN DISCH_TAC THEN
  MP_TAC(SPECL [a; `16`; `0`; `4`; `8`; s] SPONGE2_BYTES_SUB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DIV_0; MOD_0] THEN
  CONV_TAC(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC DEPTH_CONV NUM_ADD_CONV) THEN
  DISCH_TAC;;

let H_TOP87_ZERO_TAC sname =
  let s = mk_var(sname,`:armstate`) in
  MP_TAC(SPECL [H_SP87; s] SPONGE3_ZERO_STATE) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC];;

let H87_XSTATE = `keccak_f1600
   (mld_keccak_finalize 136 31
     (FST(mld_keccak_absorb 136 (word 0) 0 (in1len + in2len + in3len)
           (M1 + 2 EXP (8 * in1len) * (M2 + 2 EXP (8 * in2len) * M3))))
     ((in1len + in2len + in3len) MOD 136))`;;

(*** The four chunks of 16 bytes of the state that the copy loads ***)

let H87_CHUNK_FACTS_TAC sname =
  let s = mk_var(sname,`:armstate`) in
  FIRST_ASSUM(fun wth ->
    if not(can (term_match [] `read (memory :> wbytes a) s = x:1600 word`) (concl wth)) ||
       rand(lhand(concl wth)) <> s || rand(concl wth) <> H87_XSTATE
    then failwith "no" else
    MAP_EVERY (fun k ->
      let f = MP (SPECL [H_SP87; H87_XSTATE; mk_small_numeral k; s] SPONGE2_BYTES128_OF_WBYTES)
                 (CONJ wth (ARITH_RULE(mk_binop `(<):num->num->bool` (mk_small_numeral k) `12`))) in
      let f = CONV_RULE(DEPTH_CONV NUM_MULT_CONV) f in
      ASSUME_TAC f THEN ASSUME_TAC (SPONGE2_NORMADDR f)) (0--3));;

(*** The 64 bytes of out at the end as the SHAKE256 output ***)

let H87_OUT_TAC sname =
  let s = mk_var(sname,`:armstate`) in
  SUBGOAL_THEN
   (subst [s,`s:armstate`]
     `read (memory :> bytes(out,64)) s =
      num_of_bytelist(list_of_seq (mld_shake256_byte (in1len + in2len + in3len)
        (M1 + 2 EXP (8 * in1len) * (M2 + 2 EXP (8 * in2len) * M3))) 64)`) ASSUME_TAC THENL
   [REWRITE_TAC[SPONGE2_PH2] THEN
    MP_TAC(SPECL [`out:int64`; `4`; mk_comb(`val:1600 word->num`,H87_XSTATE); s]
                 SPONGE2_BYTES_OF_BYTES128) THEN
    ANTS_TAC THENL
     [CONV_TAC(DEPTH_CONV EXPAND_CASES_CONV) THEN
      CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
      CONV_TAC(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC DEPTH_CONV NUM_ADD_CONV) THEN
      REWRITE_TAC[WORD_ADD_0] THEN REPEAT CONJ_TAC THEN
      W(fun (_,w) -> FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = lhs w then
          (REWRITE_TAC[th] THEN REWRITE_TAC[word_subword] THEN
           CONV_TAC(DEPTH_CONV NUM_REDUCE_CONV) THEN NO_TAC) else NO_TAC));
      CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN DISCH_THEN ACCEPT_TAC];
    ALL_TAC];;

let H_TOP87_TAC h exec lem =
  ASSUME_CALLEE_SAFETY_TAILED_TAC lem.la1 "H_A1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC lem.la2 "H_A2" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC lem.la3 "H_A3" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC lem.lfin "H_FIN" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERM" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(out:int64) (in1:int64) (in1len:num) (in2:int64) (in2len:num)
     (in3:int64) (in3len:num) (guard:int64) (pc:num)
     (stackpointer:int64) (returnaddress:int64).
      f_ev_top out in1 in1len in2 in2len in3 in3len guard pc
               stackpointer returnaddress:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL; ALLPAIRS;
              PAIRWISE; NONOVERLAPPING_CLAUSES; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64) /\
                aligned 16 (word_add stackpointer (word 256):int64)`
   STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 560):int64)` THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
                        (mk_const("X"^string_of_int n,[]))) ((19--25) @ [29]) THEN
  FULL_INIT_TAC THEN
  MLD_H_BOUND_TAC `in1:int64` THEN MLD_H_BOUND_TAC `in2:int64` THEN
  MLD_H_BOUND_TAC `in3:int64` THEN
  H_LEN_TAC `560` `in1:int64` `in1len:num` THEN
  H_LEN_TAC `560` `in2:int64` `in2len:num` THEN
  H_LEN_TAC `560` `in3:int64` `in3len:num` THEN
  SUBGOAL_THEN `in1len MOD 136 < 136 /\ (in1len + in2len) MOD 136 < 136 /\
                (in1len + in2len + in3len) MOD 136 < 136`
   STRIP_ASSUME_TAC THENL [REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  ARM_STEPS_TAC exec (1--7) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC exec (8--20) THEN
  H_TOP87_PIECE_TAC "s20" THEN
  ARM_STEPS_TAC exec (21--26) THEN
  H_TOP87_ZERO_TAC "s26" THEN
  H_FULL_CALL_TAC exec "H_A1"
   [`in1:int64`; `in1len:num`; `M1:num`; H_SP87; `pc:num`] H_TOP87_VARS 27 THEN
  H_FULL_CALL_TAC exec "H_A2"
   [`in2:int64`; `in2len:num`; `M2:num`;
    `FST(mld_keccak_absorb 136 (word 0) 0 in1len M1)`; `in1len MOD 136`;
    H_SP87; `pc:num`] H_TOP87_VARS 28 THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPECL [`in1len:num`; `in2len:num`; `M1:num`; `M2:num`] MLD_SHAKE256_ABSORB_APPEND)
       (ASSUME `M1 < 2 EXP (8 * in1len)`);
    MLD_KECCAK_POS_ADD]) THEN
  H_FULL_CALL_TAC exec "H_A3"
   [`in3:int64`; `in3len:num`; `M3:num`;
    `FST(mld_keccak_absorb 136 (word 0) 0 (in1len + in2len) (M1 + 2 EXP (8 * in1len) * M2))`;
    `(in1len + in2len) MOD 136`; H_SP87; `pc:num`] H_TOP87_VARS 29 THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPECL [`in1len:num`; `in2len:num`; `in3len:num`;
               `M1:num`; `M2:num`; `M3:num`] MLD_SHAKE256_ABSORB_APPEND3)
       (CONJ (ASSUME `M1 < 2 EXP (8 * in1len)`) (ASSUME `M2 < 2 EXP (8 * in2len)`));
    MLD_KECCAK_POS_ADD; GSYM ADD_ASSOC]) THEN
  H_FULL_CALL_TAC exec "H_FIN"
   [`FST(mld_keccak_absorb 136 (word 0) 0 (in1len + in2len + in3len)
          (M1 + 2 EXP (8 * in1len) * (M2 + 2 EXP (8 * in2len) * M3)))`;
    `(in1len + in2len + in3len) MOD 136`; H_SP87; `pc:num`] H_TOP87_VARS 30 THEN
  ARM_STEPS_TAC exec (31--31) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc exec "H_PERM"
   [H_SP87;
    `mld_keccak_finalize 136 31
       (FST(mld_keccak_absorb 136 (word 0) 0 (in1len + in2len + in3len)
             (M1 + 2 EXP (8 * in1len) * (M2 + 2 EXP (8 * in2len) * M3))))
       ((in1len + in2len + in3len) MOD 136)`; `pc:num`; H_SP87; `read X30 s31`]
   H_TOP87_VARS 32 THEN
  H87_CHUNK_FACTS_TAC "s32" THEN
  ARM_STEPS_TAC exec (33--35) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC exec (36--78) THEN
  H87_OUT_TAC "s78" THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FIRST [REWRITE_TAC[] THEN NO_TAC; ASM_REWRITE_TAC[] THEN NO_TAC; H_SAFETY_TAC];;
