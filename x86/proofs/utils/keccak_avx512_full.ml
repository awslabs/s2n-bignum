(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Correctness and constant-time/memory safety in one theorem ("FULL") for   *)
(* the AVX-512VL Keccak-f1600 permutations sha3_keccak_f1600_avx512 and      *)
(* sha3_keccak4_f1600_avx512, as utils/mlkem_native2_keccak_full.ml has them *)
(* for the AVX2 ones, for callers that need both facts about the same final  *)
(* state. Each is the proof of correctness with the events: the loop taken   *)
(* from the start of an iteration to the end of the branch back, as in the   *)
(* proof of safety, and an iteration split at its rounds, the events of an   *)
(* iteration being those of its four rounds.                                 *)
(* ========================================================================= *)

needs "x86/proofs/sha3_keccak_f1600_avx512.ml";;
needs "x86/proofs/sha3_keccak4_f1600_avx512.ml";;

(* ------------------------------------------------------------------------- *)
(* The events split off the end of a goal that also has the facts of the     *)
(* correctness theorems, the latter proved by ctac; the events of the rest   *)
(* of an iteration reassociated to split off those of its next round; and    *)
(* the branch back as a condition on the iteration.                          *)
(* ------------------------------------------------------------------------- *)

let KECCAK_AVX512_EVENTS_SPLIT_TAC ctac (asl,w as gl) =
  let cs = conjuncts w in
  let ev = last cs in
  if not (is_exists ev) then failwith "KECCAK_AVX512_EVENTS_SPLIT_TAC" else
  let rest = list_mk_conj(butlast cs) in
  let th = CONJ_ACI_RULE(mk_eq(w,mk_conj(rest,ev))) in
  (GEN_REWRITE_TAC I [th] THEN
   CONJ_TAC THENL
    [ctac; ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC]) gl;;

let KECCAK_AVX512_EVENTS_REASSOC_TAC =
  CONV_TAC(ONCE_DEPTH_CONV(fun t ->
    if is_eq t && is_var(lhs t) && name_of(lhs t) = "e2"
    then RAND_CONV(REWR_CONV(GSYM APPEND_ASSOC)) t
    else failwith "KECCAK_AVX512_EVENTS_REASSOC_TAC"));;

let KECCAK_AVX512_ZF_BRANCH = prove
 (`!rc:int64 i.
     i < 6
     ==> (~(val (word_sub (word_add (word_add rc (word (32 * i))) (word 32))
                          (word_add rc (word 192))) = 0) <=> i + 1 < 6)`,
  SIMP_TAC[KECCAK_AVX512_ZF] THEN ARITH_TAC);;

let KECCAK_AVX512_WORD_COND = prove
 (`!p x y. (if p then word x else word y):int64 = word(if p then x else y)`,
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The x1 permutation sha3_keccak_f1600_avx512.                              *)
(* ------------------------------------------------------------------------- *)

let KECCAK_AVX512_FULL_ROUND_TAC r nsteps =
  KECCAK_AVX512_ROUND_GEN_TAC (TRY STRIP_EXISTS_ASSUM_TAC)
   KECCAK_AVX512_EVENTS_SPLIT_TAC
   (if r = 4 then
      MP_TAC(SPECL [`rc:int64`; `i:num`] KECCAK_AVX512_ZF_BRANCH) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(fun th ->
        REWRITE_TAC[th; KECCAK_AVX512_RSI; KECCAK_AVX512_WORD_COND])
    else ALL_TAC)
   r nsteps;;

let SHA3_KECCAK_F1600_AVX512_FULL = time prove
 (`exists f_events.
    forall e a rc A pc.
        nonoverlapping (a,200) (word pc,0xd1b) /\
        nonoverlapping (a,200) (rc,192)
        ==> ensures x86
            (\s. bytes_loaded s (word pc) sha3_keccak_f1600_avx512_tmc /\
                 read RIP s = word pc /\
                 C_ARGUMENTS [a; rc] s /\
                 wordlist_from_memory(rc,24) s = round_constants /\
                 wordlist_from_memory(a,25) s = A /\
                 read events s = e)
            (\s. read RIP s = word (pc + 0xd1a) /\
                 wordlist_from_memory(a,25) s = keccak 24 A /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc a pc /\
                      memaccess_inbounds e2 [a,200; rc,192] [a,200]))
            (MAYCHANGE [RIP; RAX; RSI] ,,
             MAYCHANGE
             [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9;
              ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15; ZMM16; ZMM17;
              ZMM18; ZMM19; ZMM20; ZMM21; ZMM22; ZMM23; ZMM24; ZMM25;
              ZMM26; ZMM27; ZMM28; ZMM29; ZMM30; ZMM31] ,,
             MAYCHANGE SOME_FLAGS ,,
             MAYCHANGE [events] ,,
             MAYCHANGE [memory :> bytes (a,200)])`,
  CONCRETIZE_F_EVENTS_TAC
   `\(rc:int64) (a:int64) (pc:num).
      APPEND (f_ev_epil rc a pc)
       (APPEND
         (ENUMERATEL 6
           (\i. APPEND (APPEND (APPEND (f_ev_r4 rc a pc i) (f_ev_r3 rc a pc i))
                               (f_ev_r2 rc a pc i))
                       (f_ev_r1 rc a pc i)))
         (f_ev_prol rc a pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `rc:int64`; `A:int64 list`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `LENGTH(A:int64 list) = 25` THENL
   [ALL_TAC;
    ENSURES_INIT_TAC "s0" THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o AP_TERM `LENGTH:int64 list->num`)) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    REWRITE_TAC[LENGTH; ARITH] THEN ASM_MESON_TAC[]] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `6` `pc + 0x95` `pc + 0xc89`
   `\i s. read RDI s = a /\
           read RSI s = word_add rc (word(32 * i)) /\
           read RAX s = word_add rc (word 192) /\
           wordlist_from_memory(rc,24) s = round_constants /\
           [word_subword (read YMM0 s) (0,64);
            word_subword (read YMM1 s) (0,64);
            word_subword (read YMM2 s) (0,64);
            word_subword (read YMM3 s) (0,64);
            word_subword (read YMM4 s) (0,64);
            word_subword (read YMM5 s) (0,64);
            word_subword (read YMM6 s) (0,64);
            word_subword (read YMM7 s) (0,64);
            word_subword (read YMM8 s) (0,64);
            word_subword (read YMM9 s) (0,64);
            word_subword (read YMM10 s) (0,64);
            word_subword (read YMM11 s) (0,64);
            word_subword (read YMM12 s) (0,64);
            word_subword (read YMM13 s) (0,64);
            word_subword (read YMM14 s) (0,64);
            word_subword (read YMM15 s) (0,64);
            word_subword (read YMM16 s) (0,64);
            word_subword (read YMM17 s) (0,64);
            word_subword (read YMM18 s) (0,64);
            word_subword (read YMM19 s) (0,64);
            word_subword (read YMM20 s) (0,64);
            word_subword (read YMM21 s) (0,64);
            word_subword (read YMM22 s) (0,64);
            word_subword (read YMM23 s) (0,64);
            word_subword (read YMM24 s) (0,64)] =
           keccak_avx512_lanes keccak_avx512_layout0 (keccak (4 * i) A)` THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;

    REWRITE_TAC[round_constants;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc,24) s:int64 list`;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(a,25) s:int64 list`] THEN
    MP_TAC(ISPEC `A:int64 list` LENGTH_EQ_25) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [th]) THEN
    REWRITE_TAC[MULT_CLAUSES; keccak; keccak_avx512_lanes;
                keccak_avx512_layout0; MAP] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    REWRITE_TAC[CONS_11; GSYM CONJ_ASSOC; WORD_ADD_0] THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC SHA3_KECCAK_F1600_AVX512_TMC_EXEC (1--26) THEN
    ENSURES_FINAL_STATE_TAC THEN
    KECCAK_AVX512_EVENTS_SPLIT_TAC
     (ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    GEN_REWRITE_TAC ONCE_DEPTH_CONV [ENUMERATEL_ADD1] THEN
    CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
    KECCAK_AVX512_EVENTS_REASSOC_TAC THEN KECCAK_AVX512_EVENTS_REASSOC_TAC THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x364`
     (keccak_avx512_assertion `keccak_avx512_layout1` `4 * i + 1`) THEN
    CONJ_TAC THENL [KECCAK_AVX512_FULL_ROUND_TAC 1 105; ALL_TAC] THEN
    KECCAK_AVX512_EVENTS_REASSOC_TAC THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x634`
     (keccak_avx512_assertion `keccak_avx512_layout2` `4 * i + 2`) THEN
    CONJ_TAC THENL [KECCAK_AVX512_FULL_ROUND_TAC 2 105; ALL_TAC] THEN
    KECCAK_AVX512_EVENTS_REASSOC_TAC THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x904`
     (keccak_avx512_assertion `keccak_avx512_layout3` `4 * i + 3`) THEN
    CONJ_TAC THENL [KECCAK_AVX512_FULL_ROUND_TAC 3 105; ALL_TAC] THEN
    KECCAK_AVX512_FULL_ROUND_TAC 4 136;

    CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(ISPECL [`A:int64 list`; `24`] LENGTH_KECCAK) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[LENGTH_EQ_25] THEN
    DISCH_THEN SUBST1_TAC THEN
    MAP_EVERY (fun k ->
      ABBREV_TAC(mk_eq(mk_var("z"^string_of_int k,`:int64`),
        list_mk_comb(`EL:num->int64 list->int64`,
          [mk_small_numeral k; `keccak 24 A`])))) (0--24) THEN
    REWRITE_TAC[keccak_avx512_lanes; keccak_avx512_layout0; MAP] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN
    REWRITE_TAC[round_constants;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc,24) s:int64 list`;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(a,25) s:int64 list`] THEN
    REWRITE_TAC[CONS_11; GSYM CONJ_ASSOC] THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    KECCAK_AVX512_HIGHS_TAC THEN
    X86_STEPS_TAC SHA3_KECCAK_F1600_AVX512_TMC_EXEC (1--26) THEN
    ENSURES_FINAL_STATE_TAC THEN
    KECCAK_AVX512_EVENTS_SPLIT_TAC
     (ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST)]);;

(*** The subroutine forms, without and with the IBT landing pad, as for
 *** SHA3_KECCAK_F1600_AVX512_NOIBT_SUBROUTINE_CORRECT and _SUBROUTINE_SAFE
 *** but with the frame of the former
 ***)

let SHA3_KECCAK_F1600_AVX512_NOIBT_SUBROUTINE_FULL = time prove
 (`exists f_events.
    forall e a rc A pc stackpointer returnaddress.
        nonoverlapping (a,200) (word pc,0xd1b) /\
        nonoverlapping (a,200) (rc,192) /\
        nonoverlapping (a,200) (stackpointer,8)
        ==> ensures x86
            (\s. bytes_loaded s (word pc) sha3_keccak_f1600_avx512_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [a; rc] s /\
                 wordlist_from_memory(rc,24) s = round_constants /\
                 wordlist_from_memory(a,25) s = A /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 wordlist_from_memory(a,25) s = keccak 24 A /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc a pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [a,200; rc,192; stackpointer,8]
                      [a,200]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,200)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  X86_ADD_RETURN_NOSTACK_TAC SHA3_KECCAK_F1600_AVX512_TMC_EXEC
   (CONV_RULE TWEAK_CONV SHA3_KECCAK_F1600_AVX512_FULL) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let SHA3_KECCAK_F1600_AVX512_SUBROUTINE_FULL = time prove
 (`exists f_events.
    forall e a rc A pc stackpointer returnaddress.
        nonoverlapping (a,200) (word pc,0xd1f) /\
        nonoverlapping (a,200) (rc,192) /\
        nonoverlapping (a,200) (stackpointer,8)
        ==> ensures x86
            (\s. bytes_loaded s (word pc) sha3_keccak_f1600_avx512_mc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [a; rc] s /\
                 wordlist_from_memory(rc,24) s = round_constants /\
                 wordlist_from_memory(a,25) s = A /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 wordlist_from_memory(a,25) s = keccak 24 A /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc a pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [a,200; rc,192; stackpointer,8]
                      [a,200]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,200)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
   (CONV_RULE TWEAK_CONV SHA3_KECCAK_F1600_AVX512_NOIBT_SUBROUTINE_FULL)));;

(* ------------------------------------------------------------------------- *)
(* The x4 permutation sha3_keccak4_f1600_avx512.                             *)
(* ------------------------------------------------------------------------- *)

let KECCAK4_AVX512_FULL_ROUND_TAC r nsteps =
  KECCAK4_AVX512_ROUND_GEN_TAC (TRY STRIP_EXISTS_ASSUM_TAC)
   KECCAK_AVX512_EVENTS_SPLIT_TAC
   (if r = 4 then
      MP_TAC(SPECL [`rc:int64`; `i:num`] KECCAK_AVX512_ZF_BRANCH) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(fun th ->
        REWRITE_TAC[th; KECCAK_AVX512_RSI; KECCAK_AVX512_WORD_COND])
    else ALL_TAC)
   r nsteps;;

let SHA3_KECCAK4_F1600_AVX512_FULL = time prove
 (`exists f_events.
    forall e a rc A1 A2 A3 A4 pc.
        nonoverlapping (a,800) (word pc,0x1073) /\
        nonoverlapping (a,800) (rc,192)
        ==> ensures x86
            (\s. bytes_loaded s (word pc) sha3_keccak4_f1600_avx512_tmc /\
                 read RIP s = word pc /\
                 C_ARGUMENTS [a; rc] s /\
                 wordlist_from_memory(rc,24) s = round_constants /\
                 wordlist_from_memory(a,25) s = A1 /\
                 wordlist_from_memory(word_add a (word 200),25) s = A2 /\
                 wordlist_from_memory(word_add a (word 400),25) s = A3 /\
                 wordlist_from_memory(word_add a (word 600),25) s = A4 /\
                 read events s = e)
            (\s. read RIP s = word(pc + 0x1072) /\
                 wordlist_from_memory(a,25) s = keccak 24 A1 /\
                 wordlist_from_memory(word_add a (word 200),25) s =
                 keccak 24 A2 /\
                 wordlist_from_memory(word_add a (word 400),25) s =
                 keccak 24 A3 /\
                 wordlist_from_memory(word_add a (word 600),25) s =
                 keccak 24 A4 /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc a pc /\
                      memaccess_inbounds e2 [a,800; rc,192] [a,800]))
            (MAYCHANGE [RIP; RAX; RSI] ,,
             MAYCHANGE
             [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9;
              ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15; ZMM16; ZMM17;
              ZMM18; ZMM19; ZMM20; ZMM21; ZMM22; ZMM23; ZMM24; ZMM25;
              ZMM26; ZMM27; ZMM28; ZMM29; ZMM30; ZMM31] ,,
             MAYCHANGE SOME_FLAGS ,,
             MAYCHANGE [events] ,,
             MAYCHANGE [memory :> bytes (a,800)])`,
  CONCRETIZE_F_EVENTS_TAC
   `\(rc:int64) (a:int64) (pc:num).
      APPEND (f_ev_epil rc a pc)
       (APPEND
         (ENUMERATEL 6
           (\i. APPEND (APPEND (APPEND (f_ev_r4 rc a pc i) (f_ev_r3 rc a pc i))
                               (f_ev_r2 rc a pc i))
                       (f_ev_r1 rc a pc i)))
         (f_ev_prol rc a pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `rc:int64`; `A1:int64 list`; `A2:int64 list`;
    `A3:int64 list`; `A4:int64 list`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC
   `LENGTH(A1:int64 list) = 25 /\ LENGTH(A2:int64 list) = 25 /\
    LENGTH(A3:int64 list) = 25 /\ LENGTH(A4:int64 list) = 25` THENL
   [FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);
    ENSURES_INIT_TAC "s0" THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o AP_TERM `LENGTH:int64 list->num`)) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    REWRITE_TAC[LENGTH; ARITH] THEN ASM_MESON_TAC[]] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `6` `pc + 0x241` `pc + 0xe35`
   `\i s. read RDI s = a /\
           read RSI s = word_add rc (word(32 * i)) /\
           read RAX s = word_add rc (word 192) /\
           wordlist_from_memory(rc,24) s = round_constants /\
           [read YMM0 s; read YMM1 s; read YMM2 s; read YMM3 s; read YMM4 s;
            read YMM5 s; read YMM6 s; read YMM7 s; read YMM8 s; read YMM9 s;
            read YMM10 s; read YMM11 s; read YMM12 s; read YMM13 s;
            read YMM14 s; read YMM15 s; read YMM16 s; read YMM17 s;
            read YMM18 s; read YMM19 s; read YMM20 s; read YMM21 s;
            read YMM22 s; read YMM23 s; read YMM24 s] =
           keccak4_avx512_regs keccak_avx512_layout0
            (keccak (4 * i) A1) (keccak (4 * i) A2)
            (keccak (4 * i) A3) (keccak (4 * i) A4)` THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;

    REWRITE_TAC[round_constants;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc,24) s:int64 list`;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(a,25) s:int64 list`;
      WORDLIST_FROM_MEMORY_CONV
       `wordlist_from_memory(word_add a (word 200),25) s:int64 list`;
      WORDLIST_FROM_MEMORY_CONV
       `wordlist_from_memory(word_add a (word 400),25) s:int64 list`;
      WORDLIST_FROM_MEMORY_CONV
       `wordlist_from_memory(word_add a (word 600),25) s:int64 list`] THEN
    MAP_EVERY (fun t ->
      MP_TAC(ISPEC t LENGTH_EQ_25) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(fun th ->
        GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [th]))
     [`A1:int64 list`; `A2:int64 list`; `A3:int64 list`; `A4:int64 list`] THEN
    REWRITE_TAC[MULT_CLAUSES; keccak; keccak4_avx512_regs;
                keccak_avx512_layout0; MAP; keccak4_lane] THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    REWRITE_TAC[CONS_11; GSYM CONJ_ASSOC; WORD_ADD_0] THEN
    ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun n ->
      let tm = if n = 0 then `read (memory :> bytes256 a) s0` else
        subst [mk_small_numeral n,`n:num`]
         `read (memory :> bytes256(word_add a (word n))) s0` in
      MP_TAC(READ_MEMORY_MERGE_CONV 2 tm) THEN
      CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC)
     (List.concat(map (fun g -> map (fun j -> 32 * g + 200 * j) (0--3))
                      (0--5))) THEN
    MAP_EVERY (fun n ->
      X86_STEPS_TAC SHA3_KECCAK4_F1600_AVX512_TMC_EXEC [n] THEN
      KECCAK_AVX2_SIMPLIFY_TAC) (1--78) THEN
    ENSURES_FINAL_STATE_TAC THEN
    KECCAK_AVX512_EVENTS_SPLIT_TAC
     (ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    GEN_REWRITE_TAC ONCE_DEPTH_CONV [ENUMERATEL_ADD1] THEN
    CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
    KECCAK_AVX512_EVENTS_REASSOC_TAC THEN KECCAK_AVX512_EVENTS_REASSOC_TAC THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x510`
     (keccak4_avx512_assertion `keccak_avx512_layout1` `4 * i + 1`) THEN
    CONJ_TAC THENL [KECCAK4_AVX512_FULL_ROUND_TAC 1 105; ALL_TAC] THEN
    KECCAK_AVX512_EVENTS_REASSOC_TAC THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x7e0`
     (keccak4_avx512_assertion `keccak_avx512_layout2` `4 * i + 2`) THEN
    CONJ_TAC THENL [KECCAK4_AVX512_FULL_ROUND_TAC 2 105; ALL_TAC] THEN
    KECCAK_AVX512_EVENTS_REASSOC_TAC THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xab0`
     (keccak4_avx512_assertion `keccak_avx512_layout3` `4 * i + 3`) THEN
    CONJ_TAC THENL [KECCAK4_AVX512_FULL_ROUND_TAC 3 105; ALL_TAC] THEN
    KECCAK4_AVX512_FULL_ROUND_TAC 4 136;


    CONV_TAC NUM_REDUCE_CONV THEN
    MAP_EVERY (fun (j,t) ->
      MP_TAC(ISPECL [t; `24`] LENGTH_KECCAK) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LENGTH_EQ_25] THEN DISCH_THEN SUBST1_TAC THEN
      MAP_EVERY (fun k ->
        ABBREV_TAC(mk_eq(
          mk_var("z"^string_of_int k^"_"^string_of_int j,`:int64`),
          list_mk_comb(`EL:num->int64 list->int64`,
            [mk_small_numeral k; list_mk_comb(`keccak`,[`24`;t])]))))
       (0--24))
     [1,`A1:int64 list`; 2,`A2:int64 list`;
      3,`A3:int64 list`; 4,`A4:int64 list`] THEN
    REWRITE_TAC[keccak4_avx512_regs; keccak_avx512_layout0; MAP;
                keccak4_lane] THEN
    CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN
    REWRITE_TAC[round_constants;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc,24) s:int64 list`;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(a,25) s:int64 list`;
      WORDLIST_FROM_MEMORY_CONV
       `wordlist_from_memory(word_add a (word 200),25) s:int64 list`;
      WORDLIST_FROM_MEMORY_CONV
       `wordlist_from_memory(word_add a (word 400),25) s:int64 list`;
      WORDLIST_FROM_MEMORY_CONV
       `wordlist_from_memory(word_add a (word 600),25) s:int64 list`] THEN
    REWRITE_TAC[CONS_11; GSYM CONJ_ASSOC] THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    MAP_EVERY (fun n ->
      X86_STEPS_TAC SHA3_KECCAK4_F1600_AVX512_TMC_EXEC [n] THEN
      KECCAK_AVX2_SIMPLIFY_TAC) (1--78) THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
      CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (can (term_match [] `read (memory :> bytes256 a) s = x`) o
             concl))) THEN
    ENSURES_FINAL_STATE_TAC THEN
    KECCAK_AVX512_EVENTS_SPLIT_TAC
     (ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST)]);;

(*** The subroutine forms, without and with the IBT landing pad ***)

let SHA3_KECCAK4_F1600_AVX512_NOIBT_SUBROUTINE_FULL = time prove
 (`exists f_events.
    forall e a rc A1 A2 A3 A4 pc stackpointer returnaddress.
        nonoverlapping (a,800) (word pc,0x1073) /\
        nonoverlapping (a,800) (rc,192) /\
        nonoverlapping (a,800) (stackpointer,8)
        ==> ensures x86
            (\s. bytes_loaded s (word pc) sha3_keccak4_f1600_avx512_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [a; rc] s /\
                 wordlist_from_memory(rc,24) s = round_constants /\
                 wordlist_from_memory(a,25) s = A1 /\
                 wordlist_from_memory(word_add a (word 200),25) s = A2 /\
                 wordlist_from_memory(word_add a (word 400),25) s = A3 /\
                 wordlist_from_memory(word_add a (word 600),25) s = A4 /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 wordlist_from_memory(a,25) s = keccak 24 A1 /\
                 wordlist_from_memory(word_add a (word 200),25) s =
                 keccak 24 A2 /\
                 wordlist_from_memory(word_add a (word 400),25) s =
                 keccak 24 A3 /\
                 wordlist_from_memory(word_add a (word 600),25) s =
                 keccak 24 A4 /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc a pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [a,800; rc,192; stackpointer,8]
                      [a,800]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,800)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  X86_ADD_RETURN_NOSTACK_TAC SHA3_KECCAK4_F1600_AVX512_TMC_EXEC
   (CONV_RULE TWEAK_CONV SHA3_KECCAK4_F1600_AVX512_FULL) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let SHA3_KECCAK4_F1600_AVX512_SUBROUTINE_FULL = time prove
 (`exists f_events.
    forall e a rc A1 A2 A3 A4 pc stackpointer returnaddress.
        nonoverlapping (a,800) (word pc,0x1077) /\
        nonoverlapping (a,800) (rc,192) /\
        nonoverlapping (a,800) (stackpointer,8)
        ==> ensures x86
            (\s. bytes_loaded s (word pc) sha3_keccak4_f1600_avx512_mc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [a; rc] s /\
                 wordlist_from_memory(rc,24) s = round_constants /\
                 wordlist_from_memory(a,25) s = A1 /\
                 wordlist_from_memory(word_add a (word 200),25) s = A2 /\
                 wordlist_from_memory(word_add a (word 400),25) s = A3 /\
                 wordlist_from_memory(word_add a (word 600),25) s = A4 /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 wordlist_from_memory(a,25) s = keccak 24 A1 /\
                 wordlist_from_memory(word_add a (word 200),25) s =
                 keccak 24 A2 /\
                 wordlist_from_memory(word_add a (word 400),25) s =
                 keccak 24 A3 /\
                 wordlist_from_memory(word_add a (word 600),25) s =
                 keccak 24 A4 /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc a pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [a,800; rc,192; stackpointer,8]
                      [a,800]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,800)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
   (CONV_RULE TWEAK_CONV SHA3_KECCAK4_F1600_AVX512_NOIBT_SUBROUTINE_FULL)));;
