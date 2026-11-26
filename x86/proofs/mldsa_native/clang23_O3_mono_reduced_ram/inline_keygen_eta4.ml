(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The unpacking of a polynomial with eta = 4 as clang 23 -O3 inlines it     *)
(* into mldsa65_pk_from_sk (mld_polyeta_unpack of ML-DSA-65, for s1 and      *)
(* s2): the 128 bytes at m + d + a0 (m the secret key in R15) become the 256 *)
(* coefficients 4 - nibble at rsp0 + ob + 8 a0, in 32 iterations of 4 bytes  *)
(* with RAX = a0 + 4 i; the words are read at [r15 + rax + d] and [r15 +     *)
(* rax + d + 2] and the vectors written at [rsp + rax * 8 + ob] and [rsp +   *)
(* rax * 8 + ob + 16]. XMM5 holds the nibble mask, XMM0 zero and XMM6 the    *)
(* four lanes of 4. The code is that of the loop of                          *)
(* mld_compute_pack_t0_t165 with other registers and addresses, and the      *)
(* proof is that of ETA4LOOP_TAC of inline_rl.ml with these parameters.      *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_keygen.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_rl.ml";;

let PKETA4_STMT fn loop exit d a0 ob =
  let da = d + a0 and ob8 = ob + 8 * a0 in
  parse_term(subst_tokens
   ["@MC@",image_mc; "@FN@",fn; "@L@",loop; "@X@",exit; "@DA@",string_of_int da;
    "@OB@",string_of_int ob8; "@A0@",string_of_int a0; "@A1@",string_of_int (a0 + 128)]
  "exists f_events.
  forall e m rsp0 pc (b:num->byte).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    aligned 16 (word_add rsp0 (word @OB@)) /\\
    ALL (nonoverlapping (word_add rsp0 (word @OB@),1024))
        [(word_add m (word @DA@),128); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) @MC@ /\\
              read RIP s = word (pc + @FN@_@L@) /\\
              read RSP s = rsp0 /\\ read R15 s = m /\\ read RAX s = word @A0@ /\\
              read XMM5 s = word 0x0f000f000f000f000f000f000f0f0f0f /\\
              read XMM0 s = word 0 /\\
              read XMM6 s = word 0x00000004000000040000000400000004 /\\
              (!j. j < 128 ==> read (memory :> bytes8 (word_add m (word (@DA@ + j)))) s = b j) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + @FN@_@X@) /\\
              read RSP s = rsp0 /\\ read R15 s = m /\\ read RAX s = word @A1@ /\\
              read XMM5 s = word 0x0f000f000f000f000f000f000f0f0f0f /\\
              read XMM0 s = word 0 /\\
              read XMM6 s = word 0x00000004000000040000000400000004 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (@OB@ + 4 * i)))) s = mld_polyeta_unpack_4 b i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events m rsp0 pc /\\
                 memaccess_inbounds e2 [word_add m (word @DA@),128; word_add rsp0 (word @OB@),1024]
                                       [word_add rsp0 (word @OB@),1024]))
         (MAYCHANGE [RIP; RAX; RCX] ,, MAYCHANGE [ZMM1; ZMM2; ZMM3; ZMM4] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(word_add rsp0 (word @OB@),1024)])");;

let pk_lin a0 = if a0 = 0 then "4 * i" else Printf.sprintf "%d + 4 * i" a0;;

let PKETA4_INV d a0 ob =
  let da = d + a0 and ob8 = ob + 8 * a0 in
  parse_term(Printf.sprintf
   "\\i s. read RSP s = rsp0 /\\ read R15 s = m /\\
          read RAX s = word (%s) /\\
          read XMM5 s = word 0x0f000f000f000f000f000f000f0f0f0f /\\
          read XMM0 s = word 0 /\\
          read XMM6 s = word 0x00000004000000040000000400000004 /\\
          (!j. j < 128 ==> read (memory :> bytes8 (word_add m (word (%d + j)))) s = (b:num->byte) j) /\\
          (!j. j < 8 * i
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = mld_polyeta_unpack_4 b j)" (pk_lin a0) da ob8);;

let PKETA4_TAC exec fn loop exit d a0 ob =
  let da = d + a0 and ob8 = ob + 8 * a0 in
  let lin = pk_lin a0 in
  let simld k = Printf.sprintf "1 * (%s) + %d" lin (d + k)
  and canld k = Printf.sprintf "4 * i + %d" (da + k) in
  let simst c = Printf.sprintf "8 * (%s) + %d" lin (ob + 16 * c)
  and canst c = Printf.sprintf "32 * i + %d" (ob8 + 16 * c) in
  let ars = if a0 = 0 then [ARITH_RULE `4 * (i + 1) = 4 * i + 4`]
            else [ARITH_RULE (parse_term(Printf.sprintf "%d + 4 * (i + 1) = (%d + 4 * i) + 4" a0 a0))] in
  CONCRETIZE_F_EVENTS_TAC
   `\(m:int64) (rsp0:int64) (pc:num).
      APPEND (f_ev_epil m rsp0 pc)
       (APPEND (ENUMERATEL 32 (\i. f_ev_loop m rsp0 pc i)) (f_ev_prol m rsp0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `m:int64`; `rsp0:int64`; `pc:num`; `b:num->byte`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit)) (PKETA4_INV d a0 ob) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN GHOST_INTRO_TAC `ymm2_init:int256` `read YMM2` THEN
    GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN GHOST_INTRO_TAC `ymm4_init:int256` `read YMM4` THEN
    FULL_INIT_TAC THEN
    XMM_EXISTSTOP_TAC "top5" `YMM5` THEN XMM_EXISTSTOP_TAC "top0" `YMM0` THEN XMM_EXISTSTOP_TAC "top6" `YMM6` THEN
    VAL_INT64_TAC (parse_term lin) THEN
    MAP_EVERY (fun k ->
      SUBGOAL_THEN (parse_term(Printf.sprintf "word_add (m:int64) (word (%s)) = word_add m (word (%s))" (simld k) (canld k))) ASSUME_TAC THENL [CP_ALIAS64_TAC; ALL_TAC]) [0;2] THEN
    MAP_EVERY (fun c ->
      SUBGOAL_THEN (parse_term(Printf.sprintf "word_add (rsp0:int64) (word (%s)) = word_add rsp0 (word (%s))" (simst c) (canst c))) ASSUME_TAC THENL [CP_ALIAS64_TAC; ALL_TAC] THEN
      ALIGN16_IDX_TAC `rsp0:int64` (parse_term(canst c)) THEN ALIGN16_IDX_TAC `rsp0:int64` (parse_term(simst c))) [0;1] THEN
    SUBGOAL_THEN (parse_term(Printf.sprintf "!k. k < 4 ==> read(memory :> bytes8(word_add m (word(%d + (4 * i + k))))) s0 = (b:num->byte)(4 * i + k)" da)) MP_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN REWRITE_TAC[ADD_CLAUSES; ADD_ASSOC] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN STRIP_TAC THEN RL_ADDR_LINEAR_TAC 4 THEN
    RL_MERGE_TAC 1 4 (parse_term(Printf.sprintf "read(memory :> bytes16(word_add m (word (%s)))) s0" (canld 0))) THEN
    RL_MERGE_TAC 1 4 (parse_term(Printf.sprintf "read(memory :> bytes16(word_add m (word (%s)))) s0" (canld 2))) THEN
    VERIF_SSE_STEPS_TAC exec (1--22) THEN X86_STEPS_TAC exec (23--25) THEN
    MAP_EVERY (fun c ->
      let lhs_tm = parse_term(Printf.sprintf "read (memory :> bytes128 (word_add (rsp0:int64) (word (%s)))) (s25:x86state)" (canst c)) in
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(SIMD_SIMPLIFY_CONV []) o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
        check (fun th -> is_eq(concl th) && aconv (lhs(concl th)) lhs_tm))) [0;1] THEN
    RL_FULL_FINAL_TAC 32 8 ars
     (REWRITE_TAC[XMM5; XMM0; XMM6; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST)
     (REWRITE_TAC[mld_polyeta_unpack_4] THEN REWRITE_TAC (ETA_DM0 @ ETA_DIVMODS) THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ADD_CLAUSES; COND_CLAUSES] THEN REPEAT CONJ_TAC THEN APP_BLAST_TAC `b:num->byte`);
    FULL_EXIT0_TAC];;

let PROVE_PKETA4 fn loop exit d a0 ob =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(PKETA4_STMT fn loop exit d a0 ob, PKETA4_TAC exec fn loop exit d a0 ob);;

