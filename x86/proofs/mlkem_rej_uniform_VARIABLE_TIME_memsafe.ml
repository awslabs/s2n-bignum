(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Memory safety for the non-constant-time rejection sampling.               *)
(*                                                                           *)
(* This proves memory safety alone (not constant-time) for                   *)
(* mlkem_rej_uniform_VARIABLE_TIME, which is intentionally not a             *)
(* constant-time function. The standard _SAFE_ proof pattern                 *)
(* (exists f_events. forall ... e2 = f_events <public_params>) cannot        *)
(* be used here because the microarchitectural events depend on private      *)
(* data (which buffer elements pass the < 3329 filter).                      *)
(*                                                                           *)
(* Note the readable range for buf is val buflen + 4, not val buflen.        *)
(* This is because the MOVDQU instruction reads 16 bytes at 12-byte          *)
(* aligned offsets within the buffer: when r8 = buflen - 12, the read        *)
(* extends to buf + buflen + 4, i.e., 4 bytes past the declared buffer.      *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_rej_uniform_VARIABLE_TIME.ml";;
needs "x86/proofs/consttime.ml";;
loadt "x86/proofs/debug.ml";;

(* Helper: discharge the memsafe postcondition
     exists e2. read events s = APPEND e2 e /\ memaccess_inbounds e2 R W
   after symbolic simulation, using accumulated events from the invariant.
   This is DISCHARGE_SAFETY_PROPERTY_TAC minus the f_events unification. *)
let DISCHARGE_MEMSAFE_TAC:tactic =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
  DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

(* Like SIMPLE_ARITH_TAC but allows `val` in assumptions since
   contained_modulo bounds may involve val terms. Filters out
   read/write/word simulation cruft that makes ASM_ARITH_TAC slow. *)
let (MEMSAFE_ARITH_TAC:tactic) =
  let numty = `:num` in
  let is_num_relop tm =
    exists (fun op -> is_binary op tm &&
                      (let x,_ = dest_binary op tm in type_of x = numty))
           ["=";"<";"<=";">";">="]
  and avoiders = ["lowdigits"; "highdigits"; "bigdigit";
                  "read"; "write"; "word"] in
  let avoiderp tm =
    match tm with Const(n,_) -> mem n avoiders | _ -> false in
  let filtered tm =
    (is_num_relop tm || (is_neg tm && is_num_relop (dest_neg tm))) &&
    not(can (find_term avoiderp) tm) in
  let tweak = GEN_REWRITE_RULE TRY_CONV [ARITH_RULE `~(n = 0) <=> 1 <= n`] in
  W(fun (asl,w) ->
    let asl' = filter (fun (_,th) -> filtered(concl th)) asl in
    MAP_EVERY (MP_TAC o tweak o snd) asl' THEN CONV_TAC ARITH_RULE);;

(* ASM-aware version of CONTAINED_TAC for loop-body proofs where
   memory addresses involve symbolic loop variables. Uses MEMSAFE_ARITH_TAC
   which filters assumptions to avoid the performance issues of ASM_ARITH_TAC
   with hundreds of symbolic simulation assumptions. *)
let CONTAINED_ASM_TAC =
  GEN_REWRITE_TAC I [GSYM CONTAINED_MODULO_MOD2] THEN
  GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV o LAND_CONV o TOP_DEPTH_CONV)
   [VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC(BINOP_CONV(LAND_CONV MOD_DOWN_CONV)) THEN
  GEN_REWRITE_TAC I [CONTAINED_MODULO_MOD2] THEN
  ((GEN_REWRITE_TAC I [CONTAINED_MODULO_REFL] THEN
    MEMSAFE_ARITH_TAC) ORELSE
   (MATCH_MP_TAC CONTAINED_MODULO_OFFSET_SIMPLE THEN
    MEMSAFE_ARITH_TAC) ORELSE
   (MATCH_MP_TAC CONTAINED_MODULO_SIMPLE THEN MEMSAFE_ARITH_TAC));;

(* ASM-aware version of DISCHARGE_MEMSAFE_TAC for loop bodies.
   Uses MEMSAFE_ARITH_TAC for contained_modulo proofs with symbolic bounds. *)
let DISCHARGE_MEMSAFE_ASM_TAC:tactic =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
  REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[memaccess_inbounds; ALL; EX; FST; SND] THEN
    REPEAT CONJ_TAC THEN
    TRY(REPEAT ((DISJ1_TAC THEN CONTAINED_ASM_TAC) ORELSE DISJ2_TAC ORELSE
                CONTAINED_ASM_TAC) THEN NO_TAC);
    REWRITE_TAC[APPEND; APPEND_NIL] THEN
    FIRST_ASSUM ACCEPT_TAC];;

let ACONV_DIAG_TAC (asl,w) =
  let n = List.length asl in
  List.iteri (fun i (_,th) ->
    let c = concl th in
    if aconv c w then
      Printf.printf "Asm %d: ACONV MATCH\n" (n - 1 - i)
    else if can (find_term (fun t ->
        try name_of t = "memaccess_inbounds" with Failure _ -> false)) c
    then begin
      Printf.printf "Asm %d: memaccess_inbounds but NOT aconv\n" (n - 1 - i);
      let ca = snd(strip_comb c) and wa = snd(strip_comb w) in
      if List.length ca = List.length wa then
        List.iteri (fun j (ct,wt) ->
          Printf.printf "  arg%d: aconv=%b type_c=%s type_w=%s\n"
            j (aconv ct wt)
            (string_of_type(type_of ct))
            (string_of_type(type_of wt)))
          (List.combine ca wa)
      else Printf.printf "  different number of args: %d vs %d\n"
        (List.length ca) (List.length wa)
    end) asl;
  ALL_TAC (asl,w);;

let MLKEM_REJ_UNIFORM_MEMSAFE = prove
 (`!res buf buflen table (inlist:(12 word)list) pc stackpointer e.
      12 divides val buflen /\
      8 * val buflen = 12 * LENGTH inlist /\
      ALL (nonoverlapping (stackpointer,528))
          [(word pc,0xf7); (buf,val buflen + 4); (table,4096)] /\
      ALL (nonoverlapping (res,512))
          [(word pc,0xf7); (stackpointer,528)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST mlkem_rej_uniform_tmc) /\
                read RIP s = word(pc + 0x7) /\
                read RSP s = stackpointer /\
                C_ARGUMENTS [res;buf;buflen;table] s /\
                (read DF s <=> false) /\
                wordlist_from_memory(table,4096) s = mlkem_rej_uniform_table /\
                wordlist_from_memory(buf,LENGTH inlist) s = inlist /\
                read events s = e)
           (\s. read RIP s = word(pc + 0xef) /\
                (exists e2.
                     read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                       [buf,val buflen + 4; table,4096; stackpointer,528]
                       [stackpointer,528; res,512]))
           (MAYCHANGE [RIP; RDI; RSI; RAX; RCX; RDX; R8; R9; R10; R11] ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(res,512);
                       memory :> bytes(stackpointer,528)])`,

  (* === Phase 0: Initial setup (same as CORRECT with extra e variable) === *)

  MAP_EVERY X_GEN_TAC [`res:int64`; `buf:int64`] THEN
  W64_GEN_TAC `buflen:num` THEN
  MAP_EVERY X_GEN_TAC
   [`table:int64`; `inlist:(12 word)list`; `pc:num`; `stackpointer:int64`;
    `e:(uarch_event)list`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              SOME_FLAGS; ALL; C_RETURN; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (* Modify precondition style, same as CORRECT *)
  MP_TAC(ISPECL
   [`table:int64`; `4096`; `4096`; `mlkem_rej_uniform_table`]
   (INST_TYPE [`:8`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
  REWRITE_TAC[DIMINDEX_8] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL
   [`buf:int64`; `LENGTH(inlist:(12 word)list)`;
    `buflen:num`; `inlist:(12 word)list`]
   (INST_TYPE [`:12`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
  ASM_REWRITE_TAC[DIMINDEX_12] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  GLOBALIZE_PRECONDITION_TAC THEN

  (* === Phase 1: Handle buflen = 0 early exit === *)

  ASM_CASES_TAC `buflen = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_MEMSAFE_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN `12 <= buflen` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN

  (* === Phase 2: Characterize N via WOP (same as CORRECT) === *)

  SUBGOAL_THEN
   `?i. buflen < 12 * (i + 1) \/
        256 <= LENGTH(REJ_SAMPLE(SUB_LIST(0,8 * i) inlist))`
  MP_TAC THENL
   [EXISTS_TAC `buflen:num` THEN ARITH_TAC;
    GEN_REWRITE_TAC LAND_CONV [num_WOP]] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_LE] THEN STRIP_TAC THEN

  SUBGOAL_THEN `~(N = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(DISJ_CASES_THEN MP_TAC) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES] THEN
    REWRITE_TAC[REJ_SAMPLE_EMPTY; LENGTH] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN

  (* === Phase 3: Main loop with event tracking === *)
  (* Invariant = CORRECT invariant + event accumulator *)

  ENSURES_WHILE_UP2_TAC `N:num` `pc + 0x73` `pc + 0xd3`
   `\i s. read RSP s = stackpointer /\
          ~read DF s /\
          read (memory :> bytes (buf,buflen)) s = num_of_wordlist inlist /\
          read(memory :> bytes(table,4096)) s =
          num_of_wordlist mlkem_rej_uniform_table /\
          read XMM0 s = word 17285419996640026625003037585112632577 /\
          read XMM4 s = word 14673634461853297750225786205640917248 /\
          read XMM5 s = word 21262780079976241823186373959458164735 /\
          read R9 s = word 0x5555 /\
          let outlist = REJ_SAMPLE(SUB_LIST(0,8 * i) inlist) in
          let outlen = LENGTH outlist in
          read RDI s = res /\
          read RSI s = buf /\
          read RDX s = word buflen /\
          read RCX s = table /\
          (i < N ==> read R8 s = word(12 * i)) /\
          read RAX s = word outlen /\
          read (memory :> bytes (stackpointer,2*outlen)) s =
          num_of_wordlist outlist /\
          (exists e_acc.
            read events s = APPEND e_acc e /\
            memaccess_inbounds e_acc
              [buf,buflen + 4; table,4096; stackpointer,528]
              [stackpointer,528; res,512])` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* === Phase 3a: Pre-loop establishes invariant at i=0 === *)

    GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
    GHOST_INTRO_TAC `ymm4_init:int256` `read YMM4` THEN
    GHOST_INTRO_TAC `ymm5_init:int256` `read YMM5` THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (1--16) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
    RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
    ASM_REWRITE_TAC[XMM0; XMM4; XMM5; READ_ZEROTOP_128] THEN
    REPEAT(CONJ_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC]) THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES; REJ_SAMPLE_EMPTY;
                LENGTH; READ_MEMORY_BYTES_TRIVIAL; num_of_wordlist] THEN
    DISCHARGE_MEMSAFE_TAC;

    (* === Phase 3b: Main loop body === *)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num`) THEN
    REWRITE_TAC[NOT_LT] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ABBREV_TAC `cur:int64 = word_add buf (word (12 * i))` THEN
    ABBREV_TAC `curlist = REJ_SAMPLE (SUB_LIST(0,8 * i) inlist)` THEN
    ABBREV_TAC `curlen = LENGTH(curlist:int16 list)` THEN
    CONV_TAC(RATOR_CONV(LAND_CONV(TOP_DEPTH_CONV let_CONV))) THEN
    ASM_REWRITE_TAC[] THEN
    GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
    GHOST_INTRO_TAC `ymm2_init:int256` `read YMM2` THEN
    GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN

    ENSURES_INIT_TAC "s0" THEN
    (* Strip the event accumulator from the invariant *)
    STRIP_EXISTS_ASSUM_TAC THEN
    XMM_EXISTSTOP_TAC "top0" `YMM0` THEN
    XMM_EXISTSTOP_TAC "top4" `YMM4` THEN
    XMM_EXISTSTOP_TAC "top5" `YMM5` THEN
    ABBREV_TAC `q0 = read (memory :> bytes128 cur) s0` THEN

    (* Simulate up to table index computation, same as CORRECT *)
    ASSUME_TAC(WORD_RULE
     `!x. word (1 * val(word x:int64)):int64 = word x`) THEN
    MAP_EVERY (fun n ->
      X86_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC [n] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_AND]) THEN
      RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV (WORD_SIMPLE_SUBWORD_CONV))) THEN
      RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV))
    (1--11) THEN

    (* Simplify, same as CORRECT *)
    RULE_ASSUM_TAC(REWRITE_RULE[lemma1a; lemma1b; WORD_BLAST
     `word_subword x (0,16):int16 = x`]) THEN
     RULE_ASSUM_TAC(REWRITE_RULE
     [MESON[] `word_subword (if p then x else y) q =
               if p then word_subword x q else word_subword y q`]) THEN
    RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [MESON[] `bit 7 (if p then x else y) =
               if p then bit 7 x else bit 7 y`]) THEN
    RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_BITVAL]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[TAUT `(if p then T else F) <=> p`]) THEN

    (* Table lookup, same as CORRECT *)
    REABBREV_TAC `idx = read R10 s11` THEN
    X86_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC [12] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_shl x 4:int64 = word(16 * val x)`]) THEN
    ABBREV_TAC
     `tab =
      read (memory :> bytes128(word_add table (word(16 * val(idx:int64)))))
           s12` THEN
    X86_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (13--14) THEN

    (* Simplify, same as CORRECT *)
    RULE_ASSUM_TAC(REWRITE_RULE[lemma2]) THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV (WORD_SIMPLE_SUBWORD_CONV))) THEN
    RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[lemma3]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BITBLAST_RULE
     `word_and ((word_zx:12 word->int16) x) (word 4095) = word_zx x`]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BITBLAST_RULE
     `word_igt (word 3329:int16) (word_zx(x:12 word)) <=>
      val(word_zx x:int16) < 3329`]) THEN

    (* Abbreviate digits, same as CORRECT *)
    ABBREV_TAC
     `(x:num->int16) j =
      word_zx(word_subword (q0:int128) (12 * j,12):12 word)` THEN
    FIRST_ASSUM(fun th ->
      MP_TAC(end_itlist CONJ (map (C SPEC th o mk_small_numeral) (0--7)))) THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN

    (* Establish table index bound for memory safety *)
    SUBGOAL_THEN `val(idx:int64) < 256` ASSUME_TAC THENL
     [EXPAND_TAC "idx" THEN
      REWRITE_TAC[bitval] THEN
      MAP_EVERY ASM_CASES_TAC
       [`val(x 0:int16) < 3329`; `val(x 1:int16) < 3329`;
        `val(x 2:int16) < 3329`; `val(x 3:int16) < 3329`;
        `val(x 4:int16) < 3329`; `val(x 5:int16) < 3329`;
        `val(x 6:int16) < 3329`; `val(x 7:int16) < 3329`] THEN
      ASM_REWRITE_TAC[bitval] THEN
      CONV_TAC(DEPTH_CONV(WORD_NUM_RED_CONV ORELSEC WORD_CONDENSE_CONV)) THEN
      CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN

    (* Relate x(j) to SUB_LIST, same as CORRECT *)
    SUBGOAL_THEN
     `!j. j < 8
          ==> (word_zx:12 word->int16)
              (EL j (SUB_LIST(8 * i,8) inlist)) = x j`
    ASSUME_TAC THENL
     [UNDISCH_THEN
       `read (memory :> bytes (buf,buflen)) s14 =
        num_of_wordlist(inlist:(12 word)list)`
       (MP_TAC o AP_TERM
         `\x. x DIV 2 EXP (8 * 12 * i) MOD 2 EXP (8 * 12)`) THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV] THEN
      REWRITE_TAC[READ_BYTES_MOD] THEN
      REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
      REWRITE_TAC[ARITH_RULE `8 * 12 = 12 * 8 * 1`] THEN
      REWRITE_TAC[ARITH_RULE `8 * 12 * x = 12 * 8 * x`] THEN
      REWRITE_TAC[GSYM DIMINDEX_12; GSYM NUM_OF_WORDLIST_SUB_LIST] THEN
      REWRITE_TAC[DIMINDEX_12] THEN
      SUBGOAL_THEN
       `MIN (buflen - 12 * i) 12 = MIN (dimindex(:128) DIV 8) 12`
      SUBST1_TAC THENL
       [REWRITE_TAC[DIMINDEX_128] THEN CONV_TAC NUM_REDUCE_CONV THEN
        MATCH_MP_TAC(ARITH_RULE
         `12 * (i + 1) <= b ==> MIN (b - 12 * i) 12 = 12`) THEN
        ASM_SIMP_TAC[];
        REWRITE_TAC[READ_COMPONENT_COMPOSE; GSYM READ_BYTES_MOD] THEN
        REWRITE_TAC[GSYM VAL_READ_WBYTES] THEN
        ASM_REWRITE_TAC[GSYM BYTES128_WBYTES; GSYM READ_COMPONENT_COMPOSE] THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN DISCH_TAC] THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
      ASM_REWRITE_TAC[word_zx; VAL_WORD_SUBWORD] THEN
      REWRITE_TAC[MULT_CLAUSES; DIMINDEX_12; ARITH_RULE `MIN n n = n`] THEN
      SUBGOAL_THEN
       `(val(q0:int128) DIV 2 EXP (12 * j)) MOD 2 EXP 12 =
        ((val q0 MOD 2 EXP 96) DIV 2 EXP (12 * j)) MOD 2 EXP 12`
       (fun th -> ASM_REWRITE_TAC[th])
      THENL
       [REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
        ASM_SIMP_TAC[ARITH_RULE
         `j < 8 ==> MIN 96 (12 * j + 12) = 12 * j + 12`];
        REWRITE_TAC[GSYM DIMINDEX_12; NUM_OF_WORDLIST_EL]] THEN
      REWRITE_TAC[LENGTH_SUB_LIST] THEN
      SIMPLE_ARITH_TAC;
      ALL_TAC] THEN

    (* Table-based selection brute force, same as CORRECT *)
    SUBGOAL_THEN
     `read YMM2 s14 =
      (word_join:int128->int128->int256)
      (word_subword (ymm2_init:int256) (128,128))
      (word(num_of_wordlist
         (FILTER (\x. val x < 3329)
                 [x 0:int16; x 1; x 2; x 3; x 4; x 5; x 6; x 7])))`
    MP_TAC THENL
     [UNDISCH_TAC
       `read(memory :> bytes(table,4096)) s14 =
        num_of_wordlist mlkem_rej_uniform_table` THEN
      REPLICATE_TAC 4
       (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
             [GSYM NUM_OF_PAIR_WORDLIST]) THEN
      REWRITE_TAC[mlkem_rej_uniform_table; pair_wordlist] THEN
      CONV_TAC WORD_REDUCE_CONV THEN
      CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
      REWRITE_TAC[GSYM BYTES128_WBYTES] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXPAND_TAC ["tab"; "idx"] THEN
      REWRITE_TAC[bitval] THEN
      MAP_EVERY ASM_CASES_TAC
       [`val(x 0:int16) < 3329`; `val(x 1:int16) < 3329`;
        `val(x 2:int16) < 3329`; `val(x 3:int16) < 3329`;
        `val(x 4:int16) < 3329`; `val(x 5:int16) < 3329`;
        `val(x 6:int16) < 3329`; `val(x 7:int16) < 3329`] THEN
      ASM_REWRITE_TAC[FILTER] THEN
      CONV_TAC(DEPTH_CONV(WORD_NUM_RED_CONV ORELSEC WORD_CONDENSE_CONV)) THEN
      ASM_REWRITE_TAC[WORD_ADD_0] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      REPLICATE_TAC 3 (ONCE_REWRITE_TAC[GSYM NUM_OF_PAIR_WORDLIST]) THEN
      REWRITE_TAC[pair_wordlist; NUM_OF_WORDLIST_SING; WORD_VAL] THEN
      REWRITE_TAC[num_of_wordlist] THEN CONV_TAC WORD_BLAST;
      DISCARD_MATCHING_ASSUMPTIONS [`read YMM2 s = x`] THEN STRIP_TAC] THEN

    (* Writeback and popcount, same as CORRECT *)
    VAL_INT64_TAC `curlen:num` THEN
    X86_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (15--16) THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV (WORD_SIMPLE_SUBWORD_CONV))) THEN

    (* Counting, same as CORRECT *)
    SUBGOAL_THEN
     `read R11 s16 = word(LENGTH (FILTER (\x. val x < 3329)
                       [x 0:int16; x 1; x 2; x 3; x 4; x 5; x 6; x 7]))`
    MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [SYM th]) THEN
      REPEAT(ONCE_REWRITE_TAC[FILTER] THEN REWRITE_TAC[] THEN
             COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
      DISCARD_STATE_TAC "s16" THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
      CONV_TAC(DEPTH_CONV(WORD_NUM_RED_CONV ORELSEC WORD_CONDENSE_CONV)) THEN
      REWRITE_TAC[LENGTH; FILTER] THEN CONV_TAC NUM_REDUCE_CONV THEN REFL_TAC;
      DISCARD_MATCHING_ASSUMPTIONS [`read R11 s = x`] THEN STRIP_TAC] THEN

    (* Overlapping writebacks, same as CORRECT *)
    MAP_EVERY ABBREV_TAC
     [`lis = FILTER (\x. val x < 3329)
                    [x 0:int16; x 1; x 2; x 3; x 4; x 5; x 6; x 7]`;
      `len = LENGTH(lis:int16 list)`] THEN

    SUBGOAL_THEN `len <= 8` ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["len"; "lis"] THEN
      REPEAT CONJ_TAC THEN
      W(MP_TAC o PART_MATCH lhand LENGTH_FILTER o lhand o snd) THEN
      REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      ALL_TAC] THEN

    ABBREV_TAC `curlist':int16 list = APPEND curlist lis` THEN
    ABBREV_TAC `curlen':num = curlen + len` THEN

    SUBGOAL_THEN
     `curlen' < 264 /\
      read (memory :> bytes (stackpointer,2*curlen')) s16 =
      num_of_wordlist(curlist':int16 list)`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["curlen'"; "curlist'"] THEN CONJ_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`curlen < 256`; `len <= 8`] THEN ARITH_TAC;
        REWRITE_TAC[LEFT_ADD_DISTRIB]] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) BYTES_EQ_NUM_OF_WORDLIST_APPEND o
        snd) THEN
      ASM_REWRITE_TAC[DIMINDEX_16; ARITH_RULE `8 * 2 * l = 16 * l`] THEN
      DISCH_THEN SUBST1_TAC THEN
      UNDISCH_THEN
       `read (memory :> bytes128 (word_add stackpointer (word (2 * curlen))))
             s16 =
        word (num_of_wordlist(lis:int16 list))`
       (MP_TAC o AP_TERM `val:int128->num`) THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES128_WBYTES; VAL_READ_WBYTES;
                  DIMINDEX_128; ARITH_RULE `128 DIV 8 = 16`] THEN
      SUBGOAL_THEN `2 * len = MIN 16 (2 * len)` SUBST1_TAC THENL
       [UNDISCH_TAC `len <= 8` THEN ARITH_TAC;
        REWRITE_TAC[GSYM READ_BYTES_MOD]] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VAL_WORD] THEN
      REWRITE_TAC[DIMINDEX_128; MOD_MOD_EXP_MIN] THEN
      MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN
      ASM_REWRITE_TAC[DIMINDEX_16] THEN
      UNDISCH_TAC `len <= 8` THEN ARITH_TAC;
      ALL_TAC] THEN

    SUBGOAL_THEN `LENGTH(curlist':int16 list) = curlen'` ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["curlist'"; "curlen'"] THEN
      REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN

    SUBGOAL_THEN `REJ_SAMPLE (SUB_LIST(8 * i,8) inlist) = lis` ASSUME_TAC THENL
     [EXPAND_TAC "lis" THEN REWRITE_TAC[REJ_SAMPLE] THEN AP_TERM_TAC THEN
      REWRITE_TAC[LIST_EQ] THEN CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN
      REWRITE_TAC[LENGTH_MAP] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [REWRITE_TAC[LENGTH_SUB_LIST] THEN MATCH_MP_TAC(ARITH_RULE
         `8 * (i + 1) <= l ==> MIN 8 (l - 8 * i) = 8`) THEN
        SIMPLE_ARITH_TAC;
        ASM_SIMP_TAC[EL_MAP] THEN DISCH_THEN(K ALL_TAC) THEN
        CONV_TAC EXPAND_CASES_CONV THEN
        CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]];
      ALL_TAC] THEN

    SUBGOAL_THEN
     `REJ_SAMPLE (SUB_LIST (0,8 * (i + 1)) inlist) = curlist'`
    ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`] THEN
      ASM_REWRITE_TAC[SUB_LIST_SPLIT; REJ_SAMPLE_APPEND; ADD_CLAUSES];
      ALL_TAC] THEN

    (* Case split over ending loop count, same structure as CORRECT *)
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [(* Case i + 1 < N: loop continues *)
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `i + 1 < N`)) THEN
      ASM_REWRITE_TAC[NOT_LT; ARITH_RULE `(i + 1) + 1 = i + 2`] THEN
      STRIP_TAC THEN VAL_INT64_TAC `curlen':num` THEN
      X86_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (17--19) THEN
      FPRINT_MSG "branch1: past steps 17-19" THEN
      (* Memsafe: protect events from GSYM WORD_ADD rewriting *)
      POP_ASSUM(fun ev_th ->
        POP_ASSUM MP_TAC THEN
        ASM_REWRITE_TAC[GSYM WORD_ADD; GSYM NOT_LT] THEN
        DISCH_TAC THEN
        ASSUME_TAC ev_th) THEN
      FPRINT_MSG "branch1: past RIP resolution" THEN
      X86_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (20--22) THEN
      FPRINT_MSG "branch1: past steps 20-22" THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(TAUT `p ==> (if p then x else y) = x`) THEN
        ASM_REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; NOT_LT; DE_MORGAN_THM] THEN
        REWRITE_TAC[WORD_RULE
         `word_add (word(12 * i)) (word 12) = word(12 * (i + 1))`] THEN
        ASM_SIMP_TAC[VAL_WORD_LE] THEN
        MAP_EVERY VAL_INT64_TAC [`buflen:num`; `12 * (i + 1)`] THEN
        ASM_REWRITE_TAC[GSYM VAL_EQ] THEN
        UNDISCH_TAC `12 * (i + 2) <= buflen` THEN ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[XMM0; XMM4; XMM5; READ_ZEROTOP_128] THEN
      REPLICATE_TAC 3 (CONJ_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC]) THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
      FPRINT_MSG "branch1: before WORD_RULE" THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      FPRINT_MSG "branch1: before DISCHARGE_MEMSAFE_ASM_TAC" THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD]) THEN
      DISCHARGE_MEMSAFE_ASM_TAC;

      (* Case i + 1 >= N: loop might exit *)
      FPRINT_MSG "branch2: entering i+1 >= N branch" THEN
      X86_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (17--19) THEN
      FPRINT_MSG "branch2: past steps 17-19" THEN
      (* Memsafe: protect events from GSYM WORD_ADD rewriting *)
      POP_ASSUM(fun ev_th ->
        POP_ASSUM MP_TAC THEN
        ASM_REWRITE_TAC[GSYM WORD_ADD; GSYM NOT_LT] THEN
        VAL_INT64_TAC `curlen':num` THEN ASM_REWRITE_TAC[NOT_LT] THEN
        COND_CASES_TAC THEN DISCH_TAC THEN
        ASSUME_TAC ev_th) THENL
       [(* Exit via JAE (outlen >= 256) *)
        FPRINT_MSG "branch2a: Exit via JAE" THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        FPRINT_MSG "branch2a: past ENSURES_FINAL_STATE_TAC" THEN
        ASM_REWRITE_TAC[XMM0; XMM4; XMM5; READ_ZEROTOP_128] THEN
        FPRINT_MSG "branch2a: past XMM rewrite" THEN
        REPLICATE_TAC 3 (CONJ_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC]) THEN
        FPRINT_MSG "branch2a: past WORD_BLAST" THEN
        CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
        ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
        FPRINT_MSG "branch2a: past GSYM WORD_ADD" THEN
        TRY(CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
        FPRINT_MSG "branch2a: before DISCHARGE_MEMSAFE_ASM_TAC" THEN
        RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD]) THEN
        DISCHARGE_MEMSAFE_ASM_TAC;

        (* Fall through to buffer exhaustion exit *)
        FPRINT_MSG "branch2b: buffer exhaustion" THEN
        X86_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (20--22) THEN
        FPRINT_MSG "branch2b: past steps 20-22" THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MATCH_MP_TAC(TAUT `p ==> (if ~p then x else y) = y`) THEN
          ASM_REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; NOT_LT; DE_MORGAN_THM] THEN
          REWRITE_TAC[WORD_RULE
           `word_add (word(12 * i)) (word 12) = word(12 * (i + 1))`] THEN
          MAP_EVERY VAL_INT64_TAC [`buflen:num`; `12 * (i + 1)`] THEN
          ASM_REWRITE_TAC[GSYM VAL_EQ; GSYM LE_LT] THEN
          FIRST_X_ASSUM(DISJ_CASES_THEN MP_TAC) THENL
           [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [divides]) THEN
            DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
            REWRITE_TAC[LE_MULT_LCANCEL; LT_MULT_LCANCEL; ARITH_EQ] THEN
            SIMPLE_ARITH_TAC;
            MATCH_MP_TAC(ARITH_RULE
             `l < 256 ==> 256 <= l ==> b <= 12 * i'`)] THEN
          DISCARD_STATE_TAC "s22" THEN
          UNDISCH_TAC `~(256 <= curlen')` THEN REWRITE_TAC[NOT_LE] THEN
          MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LET_TRANS) THEN
          SUBST1_TAC(SYM(ASSUME `LENGTH(curlist':int16 list) = curlen'`)) THEN
          EXPAND_TAC "curlist'" THEN UNDISCH_TAC `~(i + 1 < N)` THEN
          REWRITE_TAC[NOT_LT] THEN GEN_REWRITE_TAC LAND_CONV [LE_EXISTS] THEN
          DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
          REWRITE_TAC[LEFT_ADD_DISTRIB; SUB_LIST_SPLIT] THEN
          REWRITE_TAC[REJ_SAMPLE_APPEND; LENGTH_APPEND; LE_ADD];
          FPRINT_MSG "branch2b: memsafe conjunct" THEN
          ASM_REWRITE_TAC[XMM0; XMM4; XMM5; READ_ZEROTOP_128] THEN
          FPRINT_MSG "branch2b: past XMM rewrite" THEN
          REPLICATE_TAC 3 (CONJ_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC]) THEN
          FPRINT_MSG "branch2b: past WORD_BLAST" THEN
          CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
          ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
          FPRINT_MSG "branch2b: past GSYM WORD_ADD" THEN
          TRY(CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
          FPRINT_MSG "branch2b: before DISCHARGE_MEMSAFE_ASM_TAC" THEN
          RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD]) THEN
          DISCHARGE_MEMSAFE_ASM_TAC]]];

    (* === Phase 3c: Post-loop copying to output === *)

    CONV_TAC(RATOR_CONV(LAND_CONV(TOP_DEPTH_CONV let_CONV))) THEN
    MAP_EVERY ABBREV_TAC
     [`outlist = REJ_SAMPLE (SUB_LIST (0,8 * N) inlist)`;
      `outlen = LENGTH(outlist:int16 list)`] THEN
    SUBGOAL_THEN `outlen < 264` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`) THEN
      ASM_REWRITE_TAC[ARITH_RULE `n - 1 < n <=> ~(n = 0)`] THEN
      MATCH_MP_TAC(ARITH_RULE
       `l' <= l + 8 ==> ~(b < x) /\ l < 256 ==> l' < 264`) THEN
      MP_TAC(ISPECL [`inlist:(12 word)list`; `8 * (N - 1)`; `8`; `0`]
          SUB_LIST_SPLIT) THEN
      ASM_SIMP_TAC[ARITH_RULE `~(N = 0) ==> 8 * (N - 1) + 8 = 8 * N`] THEN
      MAP_EVERY EXPAND_TAC ["outlen"; "outlist"] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REJ_SAMPLE_APPEND] THEN
      REWRITE_TAC[LENGTH_APPEND; LE_ADD_LCANCEL; ADD_CLAUSES] THEN
      REWRITE_TAC[REJ_SAMPLE] THEN
      W(MP_TAC o PART_MATCH lhand LENGTH_FILTER o lhand o snd) THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LE_TRANS) THEN
      REWRITE_TAC[LENGTH_MAP; LENGTH_SUB_LIST] THEN ARITH_TAC;
      MAP_EVERY VAL_INT64_TAC [`outlen:num`; `MIN 256 outlen`]] THEN
    ENSURES_INIT_TAC "s0" THEN
    (* Strip event accumulator *)
    STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (1--3) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `word(MIN 256 outlen):int64` o MATCH_MP
     (MESON[] `read RAX s = x ==> !x'. x = x' ==> read RAX s = x'`)) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
      ONCE_REWRITE_TAC[GSYM COND_RAND] THEN AP_TERM_TAC THEN
      ASM_REWRITE_TAC[GSYM VAL_EQ] THEN CONV_TAC WORD_REDUCE_CONV THEN
      ARITH_TAC;
      DISCH_TAC] THEN
    X86_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (4--6) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_shl (word n) 1 = word(2 * n)`]) THEN
    VAL_INT64_TAC `2 * MIN 256 outlen` THEN
    X86_VSTEPS_TAC MLKEM_REJ_UNIFORM_EXEC [7] THEN
    FIRST_X_ASSUM(MP_TAC o check
      (can (term_match [] `z = read c (write c y s)`) o concl)) THEN
    SIMP_TAC[READ_WRITE_X86_STRINGCOPY; ARITH_RULE
        `2 * MIN 256 l < 2 EXP 64`] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) X86_STRINGCOPY_NONOVERLAPPING o
      rand o lhand o snd) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ARITH_TAC; NONOVERLAPPING_TAC];
      DISCH_THEN SUBST1_TAC THEN DISCH_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD]) THEN
    FPRINT_MSG "phase3c: before VAL_WORD normalization" THEN
    FPRINT THEN
    SUBGOAL_THEN `val(word buflen:int64) = buflen`
      (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN
      REWRITE_TAC[DIMINDEX_64] THEN MEMSAFE_ARITH_TAC;
      ALL_TAC] THEN
    FPRINT_MSG "phase3c: after VAL_WORD normalization" THEN
    SAFE_META_EXISTS_TAC allowed_vars_e THEN
    FPRINT_MSG "phase3c: past SAFE_META_EXISTS_TAC" THEN
    CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
    FPRINT_MSG "phase3c: past EXISTS_E2_TAC" THEN
    REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN
    FPRINT_MSG "phase3c: past MEMACCESS_INBOUNDS_APPEND" THEN
    CONJ_TAC THENL
     [FPRINT_MSG "phase3c: new events branch" THEN
      REWRITE_TAC[memaccess_inbounds; ALL; EX; FST; SND] THEN
      FPRINT_MSG "phase3c: past memaccess_inbounds unfold" THEN
      REPEAT CONJ_TAC THEN
      TRY(REPEAT ((DISJ1_TAC THEN CONTAINED_ASM_TAC) ORELSE DISJ2_TAC ORELSE
                  CONTAINED_ASM_TAC) THEN NO_TAC) THEN
      FPRINT_MSG "phase3c: CONTAINED_ASM_TAC did not solve all goals" THEN
      FPRINT;
      FPRINT_MSG "phase3c: e_acc branch" THEN
      REWRITE_TAC[APPEND; APPEND_NIL] THEN
      W(fun (asl,w) ->
        let ths = filter (fun (_,th) -> aconv (concl th) w) asl in
        let _ = Printf.printf "Found %d aconv matches\n" (List.length ths) in
        if ths = [] then failwith "CUSTOM_ACCEPT: no match"
        else let th = snd(hd ths) in
        let _ = Printf.printf "Using assumption, concl = %s\n"
          (string_of_term(concl th)) in
        ACCEPT_TAC th)]]);;

(* ------------------------------------------------------------------------- *)
(* Memory safety of the subroutine version.                                  *)
(* ------------------------------------------------------------------------- *)

let MLKEM_REJ_UNIFORM_NOIBT_SUBROUTINE_MEMSAFE = time prove
 (`!res buf buflen table (inlist:(12 word)list) pc stackpointer returnaddress e.
      12 divides val buflen /\
      8 * val buflen = 12 * LENGTH inlist /\
      ALL (nonoverlapping (word_sub stackpointer (word 528),528))
          [(word pc,LENGTH mlkem_rej_uniform_tmc);
           (buf,val buflen + 4); (table,4096)] /\
      ALL (nonoverlapping (res,512))
          [(word pc,LENGTH mlkem_rej_uniform_tmc);
           (word_sub stackpointer (word 528),536)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_rej_uniform_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [res;buf;buflen;table] s /\
                (read DF s <=> false) /\
                wordlist_from_memory(table,4096) s = mlkem_rej_uniform_table /\
                wordlist_from_memory(buf,LENGTH inlist) s = inlist /\
                read events s = e)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                (exists e2.
                     read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                       [buf,val buflen + 4; table,4096;
                        word_sub stackpointer (word 528),536]
                       [word_sub stackpointer (word 528),528; res,512]))
           (MAYCHANGE [RSP] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(res,512);
                       memory :> bytes(word_sub stackpointer (word 528),528)])`,
  let TWEAK_CONV =
    TOP_DEPTH_CONV let_CONV THENC
    REWRITE_CONV[wordlist_from_memory] in
  CONV_TAC TWEAK_CONV THEN
  X86_PROMOTE_RETURN_STACK_TAC mlkem_rej_uniform_tmc
    (CONV_RULE TWEAK_CONV MLKEM_REJ_UNIFORM_MEMSAFE) `[]` 528 THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_REJ_UNIFORM_SUBROUTINE_MEMSAFE = time prove
 (`!res buf buflen table (inlist:(12 word)list) pc stackpointer returnaddress e.
      12 divides val buflen /\
      8 * val buflen = 12 * LENGTH inlist /\
      ALL (nonoverlapping (word_sub stackpointer (word 528),528))
          [(word pc,LENGTH mlkem_rej_uniform_mc);
           (buf,val buflen + 4); (table,4096)] /\
      ALL (nonoverlapping (res,512))
          [(word pc,LENGTH mlkem_rej_uniform_mc);
           (word_sub stackpointer (word 528),536)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_rej_uniform_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [res;buf;buflen;table] s /\
                (read DF s <=> false) /\
                wordlist_from_memory(table,4096) s = mlkem_rej_uniform_table /\
                wordlist_from_memory(buf,LENGTH inlist) s = inlist /\
                read events s = e)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                (exists e2.
                     read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                       [buf,val buflen + 4; table,4096;
                        word_sub stackpointer (word 528),536]
                       [word_sub stackpointer (word 528),528; res,512]))
           (MAYCHANGE [RSP] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(res,512);
                       memory :> bytes(word_sub stackpointer (word 528),528)])`,
  let TWEAK_CONV =
    TOP_DEPTH_CONV let_CONV THENC
    REWRITE_CONV[wordlist_from_memory] in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
   (CONV_RULE TWEAK_CONV MLKEM_REJ_UNIFORM_NOIBT_SUBROUTINE_MEMSAFE)));;

(* ------------------------------------------------------------------------- *)
(* Memory safety of Windows ABI version.                                     *)
(* ------------------------------------------------------------------------- *)

let MLKEM_REJ_UNIFORM_NOIBT_WINDOWS_SUBROUTINE_MEMSAFE = time prove
 (`!res buf buflen table (inlist:(12 word)list) pc stackpointer returnaddress e.
      12 divides val buflen /\
      8 * val buflen = 12 * LENGTH inlist /\
      ALL (nonoverlapping (word_sub stackpointer (word 544),544))
          [(word pc,LENGTH mlkem_rej_uniform_windows_tmc);
           (buf,val buflen + 4); (table,4096)] /\
      ALL (nonoverlapping (res,512))
          [(word pc,LENGTH mlkem_rej_uniform_windows_tmc);
           (word_sub stackpointer (word 544),552)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_rej_uniform_windows_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [res;buf;buflen;table] s /\
                (read DF s <=> false) /\
                wordlist_from_memory(table,4096) s = mlkem_rej_uniform_table /\
                wordlist_from_memory(buf,LENGTH inlist) s = inlist /\
                read events s = e)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                (exists e2.
                     read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                       [buf,val buflen + 4; table,4096;
                        word_sub stackpointer (word 544),552]
                       [word_sub stackpointer (word 544),544; res,512]))
           (MAYCHANGE [RSP] ,,
            WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(res,512);
                       memory :> bytes(word_sub stackpointer (word 544),544)])`,
  let TWEAK_CONV =
    TOP_DEPTH_CONV let_CONV THENC
    REWRITE_CONV[wordlist_from_memory] THENC
    TOP_DEPTH_CONV DIMINDEX_CONV THENC
    ONCE_REWRITE_CONV [ARITH_RULE `x = 12 * y <=> 12 * y = x`] THENC
    SIMP_CONV[] THENC NUM_REDUCE_CONV in
  CONV_TAC TWEAK_CONV THEN
  WINDOWS_X86_WRAP_STACK_TAC
    mlkem_rej_uniform_windows_tmc mlkem_rej_uniform_tmc
    (CONV_RULE TWEAK_CONV MLKEM_REJ_UNIFORM_MEMSAFE)
    `[]` 528 THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_REJ_UNIFORM_WINDOWS_SUBROUTINE_MEMSAFE = time prove
 (`!res buf buflen table (inlist:(12 word)list) pc stackpointer returnaddress e.
      12 divides val buflen /\
      8 * val buflen = 12 * LENGTH inlist /\
      ALL (nonoverlapping (word_sub stackpointer (word 544),544))
          [(word pc,LENGTH mlkem_rej_uniform_windows_mc);
           (buf,val buflen + 4); (table,4096)] /\
      ALL (nonoverlapping (res,512))
          [(word pc,LENGTH mlkem_rej_uniform_windows_mc);
           (word_sub stackpointer (word 544),552)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_rej_uniform_windows_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [res;buf;buflen;table] s /\
                (read DF s <=> false) /\
                wordlist_from_memory(table,4096) s = mlkem_rej_uniform_table /\
                wordlist_from_memory(buf,LENGTH inlist) s = inlist /\
                read events s = e)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                (exists e2.
                     read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                       [buf,val buflen + 4; table,4096;
                        word_sub stackpointer (word 544),552]
                       [word_sub stackpointer (word 544),544; res,512]))
           (MAYCHANGE [RSP] ,,
            WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(res,512);
                       memory :> bytes(word_sub stackpointer (word 544),544)])`,
  let TWEAK_CONV =
    TOP_DEPTH_CONV let_CONV THENC
    REWRITE_CONV[wordlist_from_memory] in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
   (CONV_RULE TWEAK_CONV
     MLKEM_REJ_UNIFORM_NOIBT_WINDOWS_SUBROUTINE_MEMSAFE)));;
