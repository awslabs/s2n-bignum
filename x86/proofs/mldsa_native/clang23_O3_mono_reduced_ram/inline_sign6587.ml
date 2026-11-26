(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Generators of region lemmas for the inlined loops of the ML-DSA-65 and    *)
(* ML-DSA-87 versions of signature_internal (clang 23 -O3 mono reduced-RAM)  *)
(* that the generators of inline_sign.ml and inline_attempt.ml, written for  *)
(* mldsa44_signature_internal, do not cover as they are.                     *)
(*                                                                           *)
(* Most loops of 65 and 87 are those of 44 with other registers: clang keeps *)
(* the constant q^-1 2^32 of the Montgomery reduction in RBX, R14 or RSI     *)
(* instead of R12, the pointer to the row of w in R13 instead of RBX, and    *)
(* the temporaries of the t0 unpacking in other registers. The generators    *)
(* of 44 name those registers in their HOL terms. Rather than adding a       *)
(* parameter to each, the copies below read their terms through a renaming  *)
(* of registers: `parse_term` (which the quotations call) is shadowed while  *)
(* the copies are defined, so that every term they parse, when a lemma is    *)
(* stated or proved, has the registers of si_regmap replaced. The copies are *)
(* those of x86-C's files at c23-x86-C a5dd006da with the names suffixed     *)
(* _R; SI_WITH_REGS sets the map for one call. HROW (the hint rows) is      *)
(* copied the same way, its constants of 44 read through a map of numbers.  *)
(*                                                                           *)
(* The other differences need other code: G1AV (the slot of rho'' and the   *)
(* zeroing from XMM4), SQZV (the pointer to the state kept from before the  *)
(* loop, and a frame that covers a state above the buffer), ZERV (fewer     *)
(* instructions before the memset), ZPACK19 (the packing of z with gamma1 = *)
(* 2^19) and ETA4U (the unpacking of eta = 4).                               *)
(*                                                                           *)
(* Some code of 65 and 87 has no counterpart in 44, as gamma2 = (q - 1) / 32 *)
(* makes w1 4 bits per coefficient: DECOMP32 (the decomposition), W1PACK4G   *)
(* (the packing of w1 into the stack or through a pointer), DW1R (the row    *)
(* loop that 87 keeps rolled around both), W1UNPACK4 (the unpacking of w1    *)
(* for the hints), and C2S (87's inlined H(mu || w1), the C2 region of       *)
(* verify87 with other offsets and registers).                               *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_attempt.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_hrow.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_verify65.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_verify87.ml";;
needs "x86/proofs/utils/mldsa_native_signing.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_stage.ml";;

(* ------------------------------------------------------------------------- *)
(* The renaming of registers: whole identifiers only, the 64-bit names and   *)
(* their 32-bit halves (R12 -> RBX also maps R12D -> EBX), simultaneously.   *)
(* ------------------------------------------------------------------------- *)

let si_regmap = par_local_ref (fun () -> ([]:(string*string) list));;

let SI_REG32 r =
  match r with
    "RAX" -> "EAX" | "RBX" -> "EBX" | "RCX" -> "ECX" | "RDX" -> "EDX"
  | "RSI" -> "ESI" | "RDI" -> "EDI" | "RBP" -> "EBP" | "RSP" -> "ESP"
  | _ -> r ^ "D";;

let SI_MAP_REGS s =
  if !(si_regmap ()) = [] then s else
  let m = !(si_regmap ()) @ map (fun (a,b) -> SI_REG32 a,SI_REG32 b) !(si_regmap ()) in
  let n = String.length s in
  let isid c =
    (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') ||
    (c >= '0' && c <= '9') || c = '_' || Char.code c = 39 in
  let b = Buffer.create n in
  let i = ref 0 in
  while !i < n do
    if isid s.[!i] then
     (let j = ref !i in
      while !j < n && isid s.[!j] do incr j done;
      let w = String.sub s !i (!j - !i) in
      Buffer.add_string b (try assoc w m with Failure _ -> w);
      i := !j)
    else (Buffer.add_char b s.[!i]; incr i)
  done;
  Buffer.contents b;;

let SI_WITH_REGS m f =
  let old = !(si_regmap ()) in
  si_regmap () := m;
  try let r = f () in si_regmap () := old; r
  with e -> (si_regmap () := old; raise e);;

let si_parse_term = parse_term;;

let parse_term s = si_parse_term (SI_MAP_REGS s);;

(* ------------------------------------------------------------------------- *)
(* Copy of PWMLOOPG (inline_sign.ml): the constant in R12.                   *)
(* ------------------------------------------------------------------------- *)

let PWMLOOPG_STMT_R fn loop exit dx dy r0 =
  let ob = dx + 4 * r0 and bb = dy + 4 * r0 in
  parse_term(Printf.sprintf
  "exists f_events.
  forall e rsp0 pc (x:num->int32) (y:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    ALL (nonoverlapping (word_add rsp0 (word %d),1024))
        [(word_add rsp0 (word %d),1024); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word %d /\\ read R12 s = word 0x0380200100000000 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = x i) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = y i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word %d /\\ read R12 s = word 0x0380200100000000 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = mld_poly_pointwise_montgomery x y i) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = y i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 pc /\\
                 memaccess_inbounds e2 [word_add rsp0 (word %d),1024; word_add rsp0 (word %d),1024]
                                       [word_add rsp0 (word %d),1024]))
         (MAYCHANGE [RIP; RAX; RCX; RDX] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(word_add rsp0 (word %d),1024)])"
  ob bb image_mc fn loop r0 ob bb fn exit (r0 + 256) ob bb ob bb ob ob);;

let PWMLOOPG_TAC_R exec fn loop exit dx dy r0 =
  let ob = dx + 4 * r0 and bb = dy + 4 * r0 in
  let idx = if r0 = 0 then "2 * i" else Printf.sprintf "%d + 2 * i" r0 in
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (pc:num).
      APPEND (f_ev_epil rsp0 pc)
       (APPEND (ENUMERATEL 128 (\i. f_ev_loop rsp0 pc i)) (f_ev_prol rsp0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `pc:num`; `x:num->int32`; `y:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec; mld_poly_pointwise_montgomery] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `128` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read RSP s = rsp0 /\\ read R12 s = word 0x0380200100000000 /\\
          read RAX s = word (%s) /\\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = y j) /\\
          (!j. 2 * i <= j /\\ j < 256
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = x j) /\\
          (!j. j < 2 * i
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s =
                   mld_montgomery_reduce (word_mul (word_sx (x j)) (word_sx (y j))))" idx bb ob ob)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    VAL_INT64_TAC (parse_term idx) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MATCH_MP (CHUNK_INPUT_SPLIT_N 2) (ASSUME `i < 128`)] o
      check (fun th -> free_in `x:num->int32` (concl th) && not(free_in `mld_montgomery_reduce` (concl th)) && is_forall(concl th))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    STRIP_TAC THEN ADDR_LINEAR_BASES_TAC [ob; bb] THEN
    SUBGOAL_THEN (parse_term(Printf.sprintf "!k. k < 2 ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * (2 * i + k))))) s0 = (y:num->int32)(2 * i + k)" bb)) MP_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    STRIP_TAC THEN ADDR_LINEAR_BASES_TAC [ob; bb] THEN
    ALT_SIM_TAC
     (map (fun (c,t) -> (parse_term c, parse_term t))
        [Printf.sprintf "%d + 8 * i" ob, Printf.sprintf "4 * (%s) + %d" idx dx;
         Printf.sprintf "%d + (8 * i + 4)" ob, Printf.sprintf "4 * (%s) + %d" idx (dx + 4);
         Printf.sprintf "%d + 8 * i" bb, Printf.sprintf "4 * (%s) + %d" idx dy;
         Printf.sprintf "%d + (8 * i + 4)" bb, Printf.sprintf "4 * (%s) + %d" idx (dy + 4)]) THEN
    X86_STEPS_TAC exec (1--10) THEN RULE_ASSUM_TAC(REWRITE_RULE[PWM_MONTRED_CLANG2]) THEN
    X86_STEPS_TAC exec (11--20) THEN RULE_ASSUM_TAC(REWRITE_RULE[PWM_MONTRED_CLANG2]) THEN
    X86_STEPS_TAC exec (21--23) THEN
    CHUNKN_FULL_FINAL_TAC [ob; bb] 2
      [ARITH_RULE `2 * (i + 1) = 2 * i + 2`; ARITH_RULE (parse_term(Printf.sprintf "%d + 2 * (i + 1) = %d + 2 * i + 2" r0 r0))] ALL_TAC ALL_TAC;
    FULL_EXIT0_TAC];;

let PROVE_PWMLOOPG_R fn loop exit dx dy r0 =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(PWMLOOPG_STMT_R fn loop exit dx dy r0, PWMLOOPG_TAC_R exec fn loop exit dx dy r0);;


(* ------------------------------------------------------------------------- *)
(* Copy of T0U (inline_attempt.ml): temporaries R8 to R12, R14 and R15.      *)
(* ------------------------------------------------------------------------- *)

let T0U_STMT_R fn loop exit ob =
  parse_term(Printf.sprintf
  "exists f_events.
  forall e a rsp0 pc (b:num->byte).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    ALL (nonoverlapping (word_add rsp0 (word %d),1024))
        [(a,416); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word_add a (word 12) /\\
              read RCX s = word 28 /\\
              (!j. j < 416 ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word_add a (word 428) /\\
              read RCX s = word 1052 /\\
              (!j. j < 416 ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s =
                               mld_polyt0_unpack b i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events a rsp0 pc /\\
                 memaccess_inbounds e2 [a,416; word_add rsp0 (word %d),1024]
                                       [word_add rsp0 (word %d),1024]))
         (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11; R12; R14; R15] ,,
          MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(word_add rsp0 (word %d),1024)])"
  ob image_mc fn loop fn exit ob ob ob ob);;

let T0U_TAC_R exec fn loop exit ob =
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (rsp0:int64) (pc:num).
      APPEND (f_ev_epil a rsp0 pc)
       (APPEND (ENUMERATEL 32 (\i. f_ev_loop a rsp0 pc i)) (f_ev_prol a rsp0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `rsp0:int64`; `pc:num`; `b:num->byte`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read RSP s = rsp0 /\\
          read RAX s = word_add a (word (13 * i + 12)) /\\
          read RCX s = word (28 + 32 * i) /\\
          (!j. j < 416
               ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\\
          (!j. j < 8 * i
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s =
                   mld_polyt0_unpack b j)" ob)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0; ADD_CLAUSES] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    CHUNK_INPUT_TAC `b:num->byte` 13 THEN
    INPUT_ALT_ADDR_TAC `a:int64` THEN
    ALIAS_ASSUME_TAC T0U_ALIASES THEN
    VAL_INT64_TAC `28 + 32 * i` THEN
    X86_STEPS_TAC exec (1--102) THEN
    CHUNK_FULL_FINAL3_TAC ob
      [ARITH_RULE `13 * (i + 1) + 12 = 13 * i + 25`; ARITH_RULE `28 + 32 * (i + 1) = 28 + 32 * i + 32`]
      ALL_TAC mld_polyt0_unpack `b:num->byte`;
    FULL_EXIT0_TAC];;

let PROVE_T0U_R fn loop exit ob =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(T0U_STMT_R fn loop exit ob, T0U_TAC_R exec fn loop exit ob);;

(* ------------------------------------------------------------------------- *)
(* Copy of REDLOOPB, SUBLOOPB and ADDLOOPB (inline_attempt.ml): the row of w *)
(* at RBX.                                                                   *)
(* ------------------------------------------------------------------------- *)

let REDLOOPB_STMT_R fn loop exit =
  parse_term(Printf.sprintf
  "exists f_events.
  forall e b pc (x:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    aligned 16 b /\\ nonoverlapping (b,1024) (word pc,libmldsa_size)
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RBX s = b /\\ read RAX s = word 4 /\\
              read XMM5 s = word 0x00400000004000000040000000400000 /\\
              read XMM6 s = word 0xff801fffff801fffff801fffff801fff /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add b (word (4*i)))) s = x i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read RBX s = b /\\ read RAX s = word 260 /\\
              read XMM5 s = word 0x00400000004000000040000000400000 /\\
              read XMM6 s = word 0xff801fffff801fffff801fffff801fff /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add b (word (4*i)))) s = mld_poly_reduce x i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events b pc /\\
                 memaccess_inbounds e2 [b,1024] [b,1024]))
         (MAYCHANGE [RIP; RAX] ,, MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(b,1024)])"
  image_mc fn loop fn exit);;

let REDLOOPB_TAC_R exec fn loop exit =
  CONCRETIZE_F_EVENTS_TAC
   `\(b:int64) (pc:num).
      APPEND (f_ev_epil b pc)
       (APPEND (ENUMERATEL 32 (\i. f_ev_loop b pc i)) (f_ev_prol b pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `b:int64`; `pc:num`; `x:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec; mld_poly_reduce] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   `\i s. read RBX s = b /\
          read RAX s = word (4 + 8 * i) /\
          read XMM5 s = word 0x00400000004000000040000000400000 /\
          read XMM6 s = word 0xff801fffff801fffff801fffff801fff /\
          (!j. 8 * i <= j /\ j < 256
               ==> read(memory :> bytes32(word_add b (word(4 * j)))) s = x j) /\
          (!j. j < 8 * i
               ==> read(memory :> bytes32(word_add b (word(4 * j)))) s = mld_reduce32 (x j))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MAP_EVERY (fun n -> GHOST_INTRO_TAC (mk_var(Printf.sprintf "ymm%d_init" n,`:int256`))
                         (parse_term(Printf.sprintf "read YMM%d" n))) [0;1;2;3;4] THEN
    FULL_INIT_TAC THEN
    XMM_EXISTSTOP_TAC "top5" `YMM5` THEN XMM_EXISTSTOP_TAC "top6" `YMM6` THEN
    VAL_INT64_TAC `4 + 8 * i` THEN
    B_ALIAS_TAC "b" "4 + 8 * i" (-16) 32 0 THEN B_ALIAS_TAC "b" "4 + 8 * i" 0 32 16 THEN
    B_ALIGN_TAC "b" 32 0 THEN B_ALIGN_TAC "b" 32 16 THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MATCH_MP (CHUNK_INPUT_SPLIT_N 8) (ASSUME `i < 32`)] o
      check (fun th -> free_in `x:num->int32` (concl th) && not(free_in `mld_reduce32` (concl th)) && is_forall(concl th))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    STRIP_TAC THEN ADDR_LIN_WORD_TAC [0] THEN
    MERGE_LIN_W_TAC 2 [0] `read(memory :> bytes128(word_add b (word (0 + 32 * i)))) s0` THEN
    MERGE_LIN_W_TAC 2 [0] `read(memory :> bytes128(word_add b (word (0 + (32 * i + 16))))) s0` THEN
    VERIF_SSE_STEPS_TAC exec (1--24) THEN X86_STEPS_TAC exec (25--27) THEN
    MAP_EVERY (fun t ->
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(SIMD_SIMPLIFY_CONV []) o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
        check (fun th -> can (term_match [] `read (memory :> bytes128 a) s = x`) (concl th) &&
                         lhand(concl th) = t)))
      [`read(memory :> bytes128(word_add b (word (0 + 32 * i)))) s27`;
       `read(memory :> bytes128(word_add b (word (0 + (32 * i + 16))))) s27`] THEN
    CHUNKN_FULL_FINAL_W_TAC [0] 8
      [ARITH_RULE `8 * (i + 1) = 8 * i + 8`; ARITH_RULE `4 + 8 * (i + 1) = 4 + 8 * i + 8`]
      (REWRITE_TAC[XMM5; XMM6; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST)
      (REWRITE_TAC[REDUCE32_LANE_SSE]);
    FULL_EXIT0_TAC];;

let PROVE_REDLOOPB_R fn loop exit =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(REDLOOPB_STMT_R fn loop exit, REDLOOPB_TAC_R exec fn loop exit);;

(* mld_poly_sub x y of x at b = RBX (updated) and y at rsp0 + yb, RAX = 12 +
   16 i, x addressed as [rbx + rax * 4 - 48 + 16 g] and y as [rsp + rax * 4 +
   yb - 48 + 16 g]: the loop of w0 - c s2 *)

let SUBLOOPB_STMT_R fn loop exit yb =
  parse_term(Printf.sprintf
  "exists f_events.
  forall e b rsp0 pc (x:num->int32) (y:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    aligned 16 b /\\ aligned 16 (word_add rsp0 (word %d)) /\\
    ALL (nonoverlapping (b,1024))
        [(word_add rsp0 (word %d),1024); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RBX s = b /\\ read RSP s = rsp0 /\\ read RAX s = word 12 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add b (word (4*i)))) s = x i) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = y i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read RBX s = b /\\ read RSP s = rsp0 /\\ read RAX s = word 268 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add b (word (4*i)))) s = mld_poly_sub x y i) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = y i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events b rsp0 pc /\\
                 memaccess_inbounds e2 [b,1024; word_add rsp0 (word %d),1024] [b,1024]))
         (MAYCHANGE [RIP; RAX] ,, MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(b,1024)])"
  yb yb image_mc fn loop yb fn exit yb yb);;

let SUBLOOPB_TAC_R exec fn loop exit yb =
  let ky = yb - 48 in
  CONCRETIZE_F_EVENTS_TAC
   `\(b:int64) (rsp0:int64) (pc:num).
      APPEND (f_ev_epil b rsp0 pc)
       (APPEND (ENUMERATEL 16 (\i. f_ev_loop b rsp0 pc i)) (f_ev_prol b rsp0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `b:int64`; `rsp0:int64`; `pc:num`;
                       `x:num->int32`; `y:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec; mld_poly_sub] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `16` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read RBX s = b /\\ read RSP s = rsp0 /\\
          read RAX s = word (12 + 16 * i) /\\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = y j) /\\
          (!j. 16 * i <= j /\\ j < 256
               ==> read(memory :> bytes32(word_add b (word(4 * j)))) s = x j) /\\
          (!j. j < 16 * i
               ==> read(memory :> bytes32(word_add b (word(4 * j)))) s =
                   word_sub (x j) (y j))" yb)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MAP_EVERY (fun n -> GHOST_INTRO_TAC (mk_var(Printf.sprintf "ymm%d_init" n,`:int256`))
                         (parse_term(Printf.sprintf "read YMM%d" n))) [0;1;2;3] THEN
    FULL_INIT_TAC THEN
    VAL_INT64_TAC `12 + 16 * i` THEN
    MAP_EVERY (fun g -> B_ALIAS_TAC "b" "12 + 16 * i" (16 * g - 48) 64 (16 * g) THEN
                        B_ALIGN_TAC "b" 64 (16 * g)) [0;1;2;3] THEN
    MAP_EVERY (fun k -> ALIGN16_IDX_TAC `rsp0:int64`
        (parse_term(Printf.sprintf "4 * (12 + 16 * i) + %d" k)))
      [ky; ky + 16; ky + 32; ky + 48] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MATCH_MP (CHUNK_INPUT_SPLIT_N 16) (ASSUME `i < 16`)] o
      check (fun th -> free_in `x:num->int32` (concl th) && not(free_in `word_sub:int32->int32->int32` (concl th)) && is_forall(concl th))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    STRIP_TAC THEN ADDR_LIN_WORD_TAC [0; yb] THEN
    SUBGOAL_THEN (parse_term(Printf.sprintf "!k. k < 16 ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * (16 * i + k))))) s0 = (y:num->int32)(16 * i + k)" yb)) MP_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    STRIP_TAC THEN ADDR_LIN_WORD_TAC [0; yb] THEN
    MAP_EVERY (fun g ->
      let canon = if g = 0 then "0 + 64 * i" else Printf.sprintf "0 + (64 * i + %d)" (16 * g) in
      MERGE_LIN_W_TAC 2 [0; yb]
        (parse_term(Printf.sprintf "read(memory :> bytes128(word_add b (word (%s)))) s0" canon)) THEN
      MERGE_LIN_W_TAC 2 [0; yb]
        (parse_term(Printf.sprintf "read(memory :> bytes128(word_add rsp0 (word (4 * (12 + 16 * i) + %d)))) s0" (ky + 16 * g))))
      [0;1;2;3] THEN
    VERIF_SSE_STEPS_TAC exec (1--12) THEN X86_STEPS_TAC exec (13--15) THEN
    MAP_EVERY (fun g ->
      let canon = if g = 0 then "0 + 64 * i" else Printf.sprintf "0 + (64 * i + %d)" (16 * g) in
      let t = parse_term(Printf.sprintf "read(memory :> bytes128(word_add b (word (%s)))) s15" canon) in
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(SIMD_SIMPLIFY_CONV []) o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
        check (fun th -> lhand(concl th) = t))) [0;1;2;3] THEN
    CHUNKN_FULL_FINAL_W_TAC [0; yb] 16
      [ARITH_RULE `16 * (i + 1) = 16 * i + 16`; ARITH_RULE `12 + 16 * (i + 1) = 12 + 16 * i + 16`] ALL_TAC ALL_TAC;
    FULL_EXIT0_TAC];;

let PROVE_SUBLOOPB_R fn loop exit yb =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(SUBLOOPB_STMT_R fn loop exit yb, SUBLOOPB_TAC_R exec fn loop exit yb);;

(* mld_poly_add y x of x at rsp0 + xb and y at b = RBX (updated), RAX = 12 +
   16 i, x addressed as [rsp + rax * 4 + xb - 48 + 16 g] and y as [rbx + rax
   * 4 - 48 + 16 g]: the loop of w0 - c s2 + c t0 *)

let ADDLOOPB_STMT_R fn loop exit xb =
  parse_term(Printf.sprintf
  "exists f_events.
  forall e b rsp0 pc (x:num->int32) (y:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    aligned 16 b /\\ aligned 16 (word_add rsp0 (word %d)) /\\
    ALL (nonoverlapping (b,1024))
        [(word_add rsp0 (word %d),1024); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RBX s = b /\\ read RSP s = rsp0 /\\ read RAX s = word 12 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = x i) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add b (word (4*i)))) s = y i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read RBX s = b /\\ read RSP s = rsp0 /\\ read RAX s = word 268 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = x i) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add b (word (4*i)))) s = mld_poly_add y x i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events b rsp0 pc /\\
                 memaccess_inbounds e2 [word_add rsp0 (word %d),1024; b,1024] [b,1024]))
         (MAYCHANGE [RIP; RAX] ,, MAYCHANGE [ZMM0; ZMM1] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(b,1024)])"
  xb xb image_mc fn loop xb fn exit xb xb);;

let ADDLOOPB_TAC_R exec fn loop exit xb =
  let kx = xb - 48 in
  CONCRETIZE_F_EVENTS_TAC
   `\(b:int64) (rsp0:int64) (pc:num).
      APPEND (f_ev_epil b rsp0 pc)
       (APPEND (ENUMERATEL 16 (\i. f_ev_loop b rsp0 pc i)) (f_ev_prol b rsp0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `b:int64`; `rsp0:int64`; `pc:num`;
                       `x:num->int32`; `y:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec; mld_poly_add] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `16` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read RBX s = b /\\ read RSP s = rsp0 /\\
          read RAX s = word (12 + 16 * i) /\\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = x j) /\\
          (!j. 16 * i <= j /\\ j < 256
               ==> read(memory :> bytes32(word_add b (word(4 * j)))) s = y j) /\\
          (!j. j < 16 * i
               ==> read(memory :> bytes32(word_add b (word(4 * j)))) s =
                   word_add (y j) (x j))" xb)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MAP_EVERY (fun n -> GHOST_INTRO_TAC (mk_var(Printf.sprintf "ymm%d_init" n,`:int256`))
                         (parse_term(Printf.sprintf "read YMM%d" n))) [0;1] THEN
    FULL_INIT_TAC THEN
    VAL_INT64_TAC `12 + 16 * i` THEN
    MAP_EVERY (fun g -> B_ALIAS_TAC "b" "12 + 16 * i" (16 * g - 48) 64 (16 * g) THEN
                        B_ALIGN_TAC "b" 64 (16 * g)) [0;1;2;3] THEN
    MAP_EVERY (fun k -> ALIGN16_IDX_TAC `rsp0:int64`
        (parse_term(Printf.sprintf "4 * (12 + 16 * i) + %d" k)))
      [kx; kx + 16; kx + 32; kx + 48] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MATCH_MP (CHUNK_INPUT_SPLIT_N 16) (ASSUME `i < 16`)] o
      check (fun th -> free_in `y:num->int32` (concl th) && not(free_in `word_add:int32->int32->int32` (concl th)) && is_forall(concl th))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    STRIP_TAC THEN ADDR_LIN_WORD_TAC [0; xb] THEN
    SUBGOAL_THEN (parse_term(Printf.sprintf "!k. k < 16 ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * (16 * i + k))))) s0 = (x:num->int32)(16 * i + k)" xb)) MP_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    STRIP_TAC THEN ADDR_LIN_WORD_TAC [0; xb] THEN
    MAP_EVERY (fun g ->
      let canon = if g = 0 then "0 + 64 * i" else Printf.sprintf "0 + (64 * i + %d)" (16 * g) in
      MERGE_LIN_W_TAC 2 [0; xb]
        (parse_term(Printf.sprintf "read(memory :> bytes128(word_add b (word (%s)))) s0" canon)) THEN
      MERGE_LIN_W_TAC 2 [0; xb]
        (parse_term(Printf.sprintf "read(memory :> bytes128(word_add rsp0 (word (4 * (12 + 16 * i) + %d)))) s0" (kx + 16 * g))))
      [0;1;2;3] THEN
    VERIF_SSE_STEPS_TAC exec (1--12) THEN X86_STEPS_TAC exec (13--15) THEN
    MAP_EVERY (fun g ->
      let canon = if g = 0 then "0 + 64 * i" else Printf.sprintf "0 + (64 * i + %d)" (16 * g) in
      let t = parse_term(Printf.sprintf "read(memory :> bytes128(word_add b (word (%s)))) s15" canon) in
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(SIMD_SIMPLIFY_CONV []) o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
        check (fun th -> lhand(concl th) = t))) [0;1;2;3] THEN
    CHUNKN_FULL_FINAL_W_TAC [0; xb] 16
      [ARITH_RULE `16 * (i + 1) = 16 * i + 16`; ARITH_RULE `12 + 16 * (i + 1) = 12 + 16 * i + 16`]
      ALL_TAC (REWRITE_TAC[WORD_ADD_SYM]);
    FULL_EXIT0_TAC];;

let PROVE_ADDLOOPB_R fn loop exit xb =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(ADDLOOPB_STMT_R fn loop exit xb, ADDLOOPB_TAC_R exec fn loop exit xb);;

(* ------------------------------------------------------------------------- *)
(* Copy of HROW (inline_hrow.ml), the hint rows, for gamma2 = (q - 1) / 32   *)
(* (ML-DSA-65/87): the names _88 are those of _32, the offsets of the rows   *)
(* of w, of the packed w1 and of the counts are taken from the refs below,  *)
(* and the slot of the pointer to the signature (rsp0 + 8 in 44) is @SIGS@. *)
(* The values of the copy are thunks, so that the constants of 44 in their   *)
(* terms (omega 80, the hint bytes 2336 .. 2420, gamma2 95232, the packed w1 *)
(* at rsp0 + 800, the pointer to the hints at rsp0 + 24) are read through    *)
(* the map of the parameter set when a lemma is proved (HROW32_PSET).        *)
(* ------------------------------------------------------------------------- *)

let hr_w0 = par_local_ref (fun () -> 0x1500) and hr_wb = par_local_ref (fun () -> 192) and hr_cb = par_local_ref (fun () -> 2416) and hr_sigs = par_local_ref (fun () -> 8);;

let hrow_sub_P c s =
  subst_tokens
   ["@MC@",image_mc; "@FN@",c.hr_fn; "@K@",string_of_int c.hr_k;
    "@HEAD@",string_of_int (layout c.hr_fn + c.hr_head);
    "@STORE@",string_of_int (layout c.hr_fn + c.hr_store);
    "@FIN@",string_of_int (layout c.hr_fn + c.hr_fin);
    "@REJ@",string_of_int (layout c.hr_fn + c.hr_rej);
    "@W@",string_of_int (!(hr_w0 ()) + 1024 * c.hr_k);
    "@WB@",string_of_int (!(hr_wb ()) * c.hr_k); "@P0@",string_of_int (256 * c.hr_k);
    "@P1@",string_of_int (256 * (c.hr_k + 1)); "@CB@",string_of_int (!(hr_cb ()) + c.hr_k);
    "@SIGS@",string_of_int !(hr_sigs ())] s;;

(* The events: the iterations, each by its path (a hint that fails, in range *)
(* or not; for the other positions and for the last, a hint in range or not, *)
(* or none), and the store of the count unless a hint fails.                 *)

let HROW_TEMPLATE_P c = parse_term(hrow_sub_P c
 "\\(x:num->int32) (b:num->byte) (sig:int64) (rsp0:int64) (pc:num).
   APPEND
    (if mld_hint_count (mld_polyvec_make_hint_32 x b) @P1@ <= 80
     then f_ev_st x b sig rsp0 pc else f_ev_rj x b sig rsp0 pc)
    (APPEND
      (ENUMERATEL (glue_hint_steps 80 @P1@ (mld_polyvec_make_hint_32 x b) - @P0@)
        (\\i. if glue_hint_fail 80 (mld_polyvec_make_hint_32 x b) (@P0@ + i)
             then if glue_hint_inr_32 (x(@P0@ + i))
                  then f_ev_f2 x b sig rsp0 pc i else f_ev_f1 x b sig rsp0 pc i
             else if i < 255
             then if mld_polyvec_make_hint_32 x b (@P0@ + i)
                  then if glue_hint_inr_32 (x(@P0@ + i))
                       then f_ev_m2 x b sig rsp0 pc i else f_ev_m1 x b sig rsp0 pc i
                  else f_ev_m3 x b sig rsp0 pc i
             else if mld_polyvec_make_hint_32 x b (@P0@ + i)
                  then if glue_hint_inr_32 (x(@P0@ + i))
                       then f_ev_l2 x b sig rsp0 pc i else f_ev_l1 x b sig rsp0 pc i
                  else f_ev_l3 x b sig rsp0 pc i))
      (f_ev_pro x b sig rsp0 pc)) :(uarch_event)list");;

let HROW_STMT_P c = parse_term(hrow_sub_P c
 "exists f_events.
    forall e (x:num->int32) (b:num->byte) (sig:int64) (rsp0:int64) pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      mld_hint_count (mld_polyvec_make_hint_32 x b) @P0@ <= 80 /\\
      ALL (nonoverlapping (word_add sig (word 2336),84))
          [(word_add rsp0 (word @W@),1024); (word_add rsp0 (word 800),1024);
           (word_add rsp0 (word @SIGS@),8); (word_add rsp0 (word 24),8);
           (word pc,libmldsa_size)]
      ==> ensures x86
           (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + @HEAD@) /\\
                read RSP s = rsp0 /\\ read RCX s = word 0 /\\
                read RAX s = word (mld_hint_count (mld_polyvec_make_hint_32 x b) @P0@) /\\
                read (memory :> bytes64 (word_add rsp0 (word 24))) s = word_add sig (word 2336) /\\
                read (memory :> bytes64 (word_add rsp0 (word @SIGS@))) s = sig /\\
                (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (@W@ + 4 * i)))) s =
                                 x (@P0@ + i)) /\\
                (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (800 + 4 * i)))) s =
                                 mld_polyw1_unpack_32 (\\t. b (@WB@ + t)) i) /\\
                (!t. t < 80 ==> read (memory :> bytes8 (word_add sig (word (2336 + t)))) s =
                                mld_hint_index (mld_polyvec_make_hint_32 x b) @P0@ t) /\\
                read events s = e)
           (\\s. read RIP s =
                (if mld_hint_count (mld_polyvec_make_hint_32 x b) @P1@ <= 80
                 then word (pc + @FIN@) else word (pc + @REJ@)) /\\
                read RSP s = rsp0 /\\
                (mld_hint_count (mld_polyvec_make_hint_32 x b) @P1@ <= 80
                 ==> read RAX s = word (mld_hint_count (mld_polyvec_make_hint_32 x b) @P1@) /\\
                     (!t. t < 80 ==> read (memory :> bytes8 (word_add sig (word (2336 + t)))) s =
                                     mld_hint_index (mld_polyvec_make_hint_32 x b) @P1@ t) /\\
                     read (memory :> bytes8 (word_add sig (word @CB@))) s =
                     word (mld_hint_count (mld_polyvec_make_hint_32 x b) @P1@)) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events x b sig rsp0 pc /\\
                   memaccess_inbounds e2
                    [word_add rsp0 (word @W@),1024; word_add rsp0 (word 800),1024;
                     word_add rsp0 (word @SIGS@),8; word_add rsp0 (word 24),8;
                     word_add sig (word 2336),84]
                    [word_add sig (word 2336),84]))
           (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; RDI] ,, MAYCHANGE SOME_FLAGS ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(word_add sig (word 2336),80);
                       memory :> bytes(word_add sig (word @CB@),1)])");;

(* The invariant at the head for iteration i: the frame, and, if the code    *)
(* goes through i or there are at most 80 hints, the index, the count and    *)
(* the hint bytes so far.                                                    *)

let HROW_INV_P c = parse_term(hrow_sub_P c
 "\\i s. read RSP s = rsp0 /\\
        read (memory :> bytes64 (word_add rsp0 (word 24))) s = word_add sig (word 2336) /\\
        read (memory :> bytes64 (word_add rsp0 (word @SIGS@))) s = sig /\\
        (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (@W@ + 4 * i)))) s =
                         x (@P0@ + i)) /\\
        (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (800 + 4 * i)))) s =
                         mld_polyw1_unpack_32 (\\t. b (@WB@ + t)) i) /\\
        (i < glue_hint_steps 80 @P1@ (mld_polyvec_make_hint_32 x b) - @P0@ \\/
         mld_hint_count (mld_polyvec_make_hint_32 x b) @P1@ <= 80
         ==> read RCX s = word i /\\
             read RAX s = word (mld_hint_count (mld_polyvec_make_hint_32 x b) (@P0@ + i)) /\\
             (!t. t < 80 ==> read (memory :> bytes8 (word_add sig (word (2336 + t)))) s =
                             mld_hint_index (mld_polyvec_make_hint_32 x b) (@P0@ + i) t))");;

let HROW_EXEC_P c =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [(layout c.hr_fn + c.hr_head - c.hr_lo, layout c.hr_fn + c.hr_fin)];;

(* ------------------------------------------------------------------------- *)
(* Arithmetic and the forms of the simulation.                               *)
(* ------------------------------------------------------------------------- *)

(*** The row has at least one iteration if the count before it fits ***)

let HROW_STEPS_POS_P () = prove
 (`!h omega p0 p1. p0 < p1 /\ mld_hint_count h p0 <= omega
                   ==> p0 < glue_hint_steps omega p1 h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[glue_hint_steps] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`h:num->bool`; `omega:num`; `p1:num`] GLUE_HINT_FAIL_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?p. glue_hint_fail omega (h:num->bool) p` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [MINIMAL] THEN BETA_TAC THEN
  ABBREV_TAC `m = minimal p. glue_hint_fail omega (h:num->bool) p` THEN
  REWRITE_TAC[glue_hint_fail] THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `p0 < m + 1 <=> ~(m < p0)`] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`h:num->bool`; `m + 1`; `p0:num`] MLD_HINT_COUNT_MONO) THEN
  ASM_REWRITE_TAC[MLD_HINT_COUNT_ADD1] THEN ASM_ARITH_TAC);;

let HROW_DIVMOD_P () = prove
 (`!k i. i < 256 ==> (256 * k + i) DIV 256 = k /\ (256 * k + i) MOD 256 = i`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `i:num`;
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `k:num`] THEN ASM_ARITH_TAC);;

(*** The range test (ja): x - (2^32 - gamma2) compared with 2 gamma2 ***)

let HROW_SUB_G2_32_P () = prove
 (`!a:int32. word_sub a (word 4294872064) = word_add a (word 95232)`,
  GEN_TAC THEN SUBGOAL_THEN `word 4294872064:int32 = word_neg(word 95232)` SUBST1_TAC THENL
   [CONV_TAC WORD_REDUCE_CONV; CONV_TAC WORD_RULE]);;

let HROW_JA_P () = prove
 (`!v:int32.
     (~(~(&(val v) - &190464:int = &(val(word_sub v (word 190464)))) \/
        val(word_sub v (word 190464)) = 0)) <=> ~(val v <= 190464)`,
  GEN_TAC THEN MP_TAC(SPECL [`v:int32`; `190464`] GLUE_FLAGS_LS) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC TAUT);;

(*** The test in range (or of SETNE and SETE, jne) ***)

let HROW_BYTE_JOIN_P () = prove
 (`!(h:56 word) (b:byte). word(val(word_join h b:int64) MOD 256):byte = b`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `word(val(word_join h b:int64) MOD 256):byte = word_zx(word_join h b:int64)`
  SUBST1_TAC THENL
   [REWRITE_TAC[word_zx; GSYM VAL_EQ; VAL_WORD; DIMINDEX_8] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL];
    CONV_TAC WORD_BLAST]);;

let HROW_JNE_P () = prove
 (`!(h1:56 word) (h2:56 word) A B.
     val(word(val(word_join h1 (if A then word 1 else word 0:byte):int64) MOD 256) ||
         word(val(word_join h2 (if B then word 1 else word 0:byte):int64) MOD 256):byte) = 0
     <=> ~A /\ ~B`,
  REPEAT GEN_TAC THEN REWRITE_TAC[(HROW_BYTE_JOIN_P ())] THEN
  MAP_EVERY BOOL_CASES_TAC [`A:bool`; `B:bool`] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

let HROW_ADDG2_EQ0_P () = prove
 (`!a:int32. val(word_add a (word 95232)) = 0 <=> a = word 4294872064`,
  GEN_TAC THEN REWRITE_TAC[VAL_EQ_0] THEN
  SUBGOAL_THEN `word 4294872064:int32 = word_neg(word 95232)` SUBST1_TAC THENL
   [CONV_TAC WORD_REDUCE_CONV; CONV_TAC WORD_RULE]);;

(*** The test of the count (je), its copy to EDX and its increment ***)

let HROW_CNT80_P () = prove
 (`!n. n <= 80
       ==> (val(word_sub (word_zx (word n:int64):int32) (word 80)) = 0 <=> n = 80)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `n MOD 18446744073709551616 = n` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `n MOD 4294967296 = n` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; REFL_TAC]);;

let HROW_ZX_SMALL_P () = prove
 (`!n. n < 2 EXP 32 ==> word_zx (word_zx (word n:int64):int32):int64 = word n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `n MOD 18446744073709551616 = n /\ n MOD 4294967296 = n`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_REWRITE_TAC[]]);;

let HROW_INC32_P () = prove
 (`!n. n < 80
       ==> word_zx (word_add (word_zx (word n:int64):int32) (word 1)):int64 =
           word (n + 1)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `n MOD 18446744073709551616 = n /\ n MOD 4294967296 = n /\
                (n + 1) MOD 4294967296 = n + 1 /\
                (n + 1) MOD 18446744073709551616 = n + 1`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

let HROW_VAL_BYTE_P () = prove
 (`!n. word(val(word n:int64) MOD 256):byte = word n`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_8; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `18446744073709551616 = 256 * 72057594037927936`;
              MOD_MOD; MOD_MOD_REFL]);;

(*** The test of the index (je after inc rcx; cmp rcx, 256) ***)

let HROW_LAST_P () = prove
 (`!i. i < 256
       ==> (val(word_add (word i:int64) (word 18446744073709551361)) = 0 <=>
            ~(i < 255))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `i MOD 18446744073709551616 = i` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `i < 255` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `(i + 18446744073709551361) MOD 18446744073709551616 =
                  i + 18446744073709551361`
    SUBST1_TAC THENL [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ARITH_TAC];
    SUBGOAL_THEN `i = 255` SUBST1_TAC THENL
     [ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]]);;

(* ------------------------------------------------------------------------- *)
(* Tactics for the paths of an iteration.                                    *)
(* ------------------------------------------------------------------------- *)

let hrow_num_P k n = mk_small_numeral(n k);;
let HROW_CNT_TM_P k = subst [mk_small_numeral(256 * k),`P0:num`]
  `mld_hint_count (mld_polyvec_make_hint_32 x b) (P0 + i)`;;
let HROW_FAIL_TM_P k = subst [mk_small_numeral(256 * k),`P0:num`]
  `glue_hint_fail 80 (mld_polyvec_make_hint_32 x b) (P0 + i)`;;
let HROW_H_TM_P k = subst [mk_small_numeral(256 * k),`P0:num`]
  `mld_polyvec_make_hint_32 x b (P0 + i)`;;
let HROW_INR_TM_P k = subst [mk_small_numeral(256 * k),`P0:num`]
  `glue_hint_inr_32 (x (P0 + i))`;;
let HROW_STEPS_TM_P k = subst [mk_small_numeral(256 * (k + 1)),`P1:num`]
  `glue_hint_steps 80 P1 (mld_polyvec_make_hint_32 x b)`;;

(*** The fact for position i of a forall fact matching pat, rewritten ***)

let HROW_SPEC_TAC_P pat eqs =
  FIRST_ASSUM(fun th -> if can (term_match [] pat) (concl th) then
    MP_TAC(SPEC `i:num` th) THEN ANTS_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN(ASSUME_TAC o REWRITE_RULE eqs)]
    else NO_TAC);;

(*** A conditional branch: its condition, in the RIP fact, as target ***)

let HROW_RIP_COND_P (asl,w) =
  let ths = filter (fun (_,th) -> let c = concl th in
     is_eq c && can (term_match [] `read RIP s`) (lhs c) && is_cond (rhs c)) asl in
  fst(dest_cond (rhs(concl(snd(hd ths)))));;

let HROW_DECIDE_TAC_P target prover =
  W(fun (asl,w) -> let c = HROW_RIP_COND_P (asl,w) in
     SUBGOAL_THEN (mk_iff(c,target)) (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
      [prover; ALL_TAC]);;

(*** Cases on t, rewriting the other assumptions with the case ***)

let HROW_CASES_TAC_P t =
  ASM_CASES_TAC t THEN
  FIRST_ASSUM(fun th -> if concl th = t || concl th = mk_neg t
    then RULE_ASSUM_TAC(fun th' -> if concl th' = concl th then th'
                                   else REWRITE_RULE[th] th')
    else NO_TAC);;

(*** The hint bit of position 256 k + i from the coefficients, as a fact, ***)
(*** used for the tests and then dropped (it would rewrite the predicate ***)
(*** in the template)                                                    ***)

let HROW_UNFOLD_TAC_P k =
  let p0 = mk_small_numeral(256 * k) and wb = mk_small_numeral(!(hr_wb ()) * k) in
  let th = CONV_RULE NUM_REDUCE_CONV
    (MP (SPECL [mk_small_numeral k; `i:num`] (HROW_DIVMOD_P ())) (ASSUME `i < 256`)) in
  let t = subst [p0,`P0:num`; wb,`WB:num`]
   `mld_polyvec_make_hint_32 x b (P0 + i) <=>
    mld_make_hint_32 (x (P0 + i)) (mld_polyw1_unpack_32 (\t. b (WB + t)) i)` in
  SUBGOAL_THEN t ASSUME_TAC THENL
   [REWRITE_TAC[GLUE_POLYVEC_HINT_32; th] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[];
    ALL_TAC];;

let is_hrow_unfold_P th =
  is_iff(concl th) && can (find_term ((=) `mld_make_hint_32`)) (concl th);;

let HROW_DROP_UNFOLD_TAC_P () =
  FIRST_X_ASSUM(K ALL_TAC o check is_hrow_unfold_P);;

let HROW_HINT_INR_TAC_P () =
  FIRST_ASSUM(fun th -> if is_hrow_unfold_P th then REWRITE_TAC[th] else NO_TAC) THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) GLUE_HINT_INR_32
      (find_term (fun t -> can (term_match [] `mld_make_hint_32 a b`) t) w))) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN CONV_TAC TAUT;;

let HROW_HINT_OUT_TAC_P k =
  SUBGOAL_THEN (HROW_H_TM_P k) ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_hrow_unfold_P th then REWRITE_TAC[th] else NO_TAC) THEN
    MATCH_MP_TAC GLUE_HINT_OUT_32 THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC];;

(*** The next position (GLUE_HINT_NEXT): the number of iterations and the ***)
(*** count of the row, in the cases of a failure, of another position and ***)
(*** of the last                                                         ***)

let HROW_IDX_ARITH_TAC_P () =
  MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`i < 255`; `~(i < 255)`; `i < 256`] THEN
  ARITH_TAC;;

let HROW_NOFAIL_TAC_P () =
  FIRST_ASSUM ACCEPT_TAC ORELSE (REWRITE_TAC[glue_hint_fail] THEN ASM_REWRITE_TAC[]);;

let HROW_NEXT_TAC_P p0 p1 =
  let p = mk_binop `(+):num->num->num` (mk_small_numeral p0) `i:num` in
  MP_TAC(SPECL [`mld_polyvec_make_hint_32 x b`; `80`; mk_small_numeral p1; p]
               GLUE_HINT_NEXT) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  W(fun (asl,w) ->
    let fl = list_mk_comb(`glue_hint_fail 80 (mld_polyvec_make_hint_32 x b)`,[p]) in
    let has t = exists (fun (_,th) -> concl th = t) asl in
    if has fl then DISCH_THEN(MP_TAC o C MP (ASSUME fl) o CONJUNCT1) THEN STRIP_TAC
    else
    (if has (mk_neg fl) then ALL_TAC
     else SUBGOAL_THEN (mk_neg fl) ASSUME_TAC THENL [(HROW_NOFAIL_TAC_P ()); ALL_TAC]) THEN
    if has `~(i < 255)` then
      DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
      ANTS_TAC THENL [CONJ_TAC THENL [(HROW_NOFAIL_TAC_P ()); (HROW_IDX_ARITH_TAC_P ())]; STRIP_TAC]
    else
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
      ANTS_TAC THENL [CONJ_TAC THENL [(HROW_NOFAIL_TAC_P ()); (HROW_IDX_ARITH_TAC_P ())]; STRIP_TAC]);;

(*** The count below 80 on the path of a hint that fits: EDX and the store ***)
(*** address from it                                                      ***)

let HROW_CNT_FACTS_TAC_P (cnt:term) =
  let lt80 = mk_binop `(<):num->num->bool` cnt `80` in
  let lt80_tac = FIRST_ASSUM(MP_TAC o check (fun th -> concl th = lt80)) THEN ARITH_TAC in
  SUBGOAL_THEN lt80 ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
       can (term_match [] `glue_hint_fail 80 h p`) (rand(concl th)))) THEN
    REWRITE_TAC[glue_hint_fail] THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o check (fun th ->
      concl th = mk_binop `(<=):num->num->bool` cnt `80`)) THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`word_zx:int32->int64`,
                       mk_comb(`word_zx:int64->int32`,mk_comb(`word:num->int64`,cnt))),
                      mk_comb(`word:num->int64`,cnt))) ASSUME_TAC THENL
   [MATCH_MP_TAC (HROW_ZX_SMALL_P ()) THEN lt80_tac; ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,mk_comb(`word:num->int64`,cnt)),cnt))
  ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN lt80_tac;
    ALL_TAC];;

(*** The end of an iteration: the next invariant and the events ***)

let HROW_STEPS_LT_TAC_P p0 p1 =
  let tm = subst [mk_small_numeral p0,`P0:num`; mk_small_numeral p1,`P1:num`]
   `i + 1 < glue_hint_steps 80 P1 (mld_polyvec_make_hint_32 x b) - P0 <=>
    (P0 + i) + 1 < glue_hint_steps 80 P1 (mld_polyvec_make_hint_32 x b)` in
  SUBGOAL_THEN tm SUBST1_TAC THENL [ARITH_TAC; ALL_TAC];;

let HROW_BYTES_TAC_P k =
  let th = CONV_RULE NUM_REDUCE_CONV
    (MP (SPECL [mk_small_numeral k; `i:num`] (HROW_DIVMOD_P ())) (ASSUME `i < 256`)) in
  X_GEN_TAC `t:num` THEN DISCH_TAC THEN REWRITE_TAC[MLD_HINT_INDEX_ADD1] THEN
  ASM_REWRITE_TAC[] THEN
  TRY(COND_CASES_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_eq o concl)) THEN ASM_REWRITE_TAC[] THEN
    AP_TERM_TAC THEN REWRITE_TAC[CONJUNCT2 th] THEN MATCH_MP_TAC MOD_LT THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC]) THEN
  TRY(FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let HROW_EVENTS_TAC_P () =
  REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let HROW_REGS_TAC_P () =
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD; MULT_CLAUSES]) THEN
  TRY(FIRST_ASSUM(fun th ->
    if is_comb(concl th) && can (term_match [] `mld_hint_count h p < 80`) (concl th)
    then RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP (HROW_INC32_P ()) th]) else NO_TAC));;

let HROW_FINAL_TAC_P k =
  (HROW_REGS_TAC_P ()) THEN
  HROW_NEXT_TAC_P (256 * k) (256 * (k + 1)) THEN ENSURES_FINAL_STATE_TAC THEN
  HROW_STEPS_LT_TAC_P (256 * k) (256 * (k + 1)) THEN
  ASM_REWRITE_TAC[GSYM ADD_ASSOC; LT_REFL] THEN
  REWRITE_TAC[ADD_ASSOC; MLD_HINT_COUNT_ADD1] THEN ASM_REWRITE_TAC[ADD_0] THEN
  REPEAT CONJ_TAC THEN
  TRY(HROW_BYTES_TAC_P k THEN NO_TAC) THEN
  (HROW_EVENTS_TAC_P ());;

(*** The test of the index from step n, and the end of the iteration ***)

let HROW_LOOPTEST_TAC_P ex k n =
  X86_STEPS_TAC ex (n--(n+2)) THEN
  HROW_DECIDE_TAC_P `~(i < 255)` (MATCH_MP_TAC (HROW_LAST_P ()) THEN FIRST_ASSUM ACCEPT_TAC) THEN
  HROW_CASES_TAC_P `i < 255` THEN HROW_FINAL_TAC_P k;;

(*** The path of a hint from the test of the count at step n; jmp = 1 if ***)
(*** the code jumps back to the test of the index                        ***)

let HROW_HINT_PATH_TAC_P ex k jmp n =
  let cnt = HROW_CNT_TM_P k and fl = HROW_FAIL_TM_P k in
  let cntz = mk_eq(mk_comb(`word_zx:int32->int64`,
                    mk_comb(`word_zx:int64->int32`,mk_comb(`word:num->int64`,cnt))),
                   mk_comb(`word:num->int64`,cnt)) in
  let excl = vsubst [cnt,`c:num`; mk_small_numeral(256 * k),`P0:num`]
   `!t. t < 80 /\ ~(t = c)
        ==> read(memory :> bytes8(word_add sig (word(2336 + t)))) s =
            mld_hint_index (mld_polyvec_make_hint_32 x b) (P0 + i) t` in
  X86_STEPS_TAC ex (n--(n+1)) THEN
  HROW_DECIDE_TAC_P fl
   (REWRITE_TAC[glue_hint_fail; ASSUME (HROW_H_TM_P k)] THEN MATCH_MP_TAC (HROW_CNT80_P ()) THEN
    FIRST_ASSUM ACCEPT_TAC) THEN
  HROW_CASES_TAC_P fl THENL
   [HROW_FINAL_TAC_P k;
    HROW_CNT_FACTS_TAC_P cnt THEN
    W(fun (asl,w) ->
      let s = mk_var("s"^string_of_int(n+1),`:x86state`) in
      SUBGOAL_THEN (vsubst [s,`s:x86state`] excl) ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC]) THEN
    X86_STEPS_TAC ex [n+2] THEN RULE_ASSUM_TAC(REWRITE_RULE[ASSUME cntz]) THEN
    X86_STEPS_TAC ex ((n+3)--(n+5+jmp)) THEN
    HROW_LOOPTEST_TAC_P ex k (n+6+jmp)];;

(*** An iteration ***)

let HROW_BODY_TAC_P c ex =
  let k = c.hr_k in
  let p0 = mk_small_numeral(256 * k) and w = !(hr_w0 ()) + 1024 * k in
  let steps = HROW_STEPS_TM_P k in
  let n = mk_binop `(-):num->num->num` steps p0 in
  let lt_n = mk_binop `(<):num->num->bool` `i:num` n in
  let p_lt = mk_binop `(<):num->num->bool` (mk_binop `(+):num->num->num` p0 `i:num`) steps in
  let late = if c.hr_late then 1 else 0 in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN p_lt ASSUME_TAC THENL
   [UNDISCH_TAC lt_n THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `i < 256` ASSUME_TAC THENL
   [UNDISCH_TAC p_lt THEN
    FIRST_ASSUM(MP_TAC o check (fun th ->
      concl th = mk_binop `(<=):num->num->bool` steps (mk_small_numeral(256 * (k + 1))))) THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (mk_binop `(<=):num->num->bool` (HROW_CNT_TM_P k) `80`) ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (term_match [] `!p. p < n ==> mld_hint_count h p <= 80`) (concl th))) THEN
    FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[ASSUME lt_n] THEN
  GHOST_INTRO_TAC `rdx_init:int64` `read RDX` THEN
  GHOST_INTRO_TAC `rsi_init:int64` `read RSI` THEN
  FULL_INIT_TAC THEN
  HROW_SPEC_TAC_P (parse_term(Printf.sprintf
    "!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4 * i)))) s0 = y i" w))
    [ARITH_RULE(parse_term(Printf.sprintf "%d + 4 * i = 4 * i + %d" w w))] THEN
  HROW_SPEC_TAC_P
    `!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (800 + 4 * i)))) s0 = y i`
    [ARITH_RULE `800 + 4 * i = 4 * i + 800`] THEN
  VAL_INT64_TAC `i:num` THEN
  X86_STEPS_TAC ex (1--7) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; (HROW_SUB_G2_32_P ())]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[(HROW_JA_P ()); GLUE_INR_32]) THEN
  HROW_UNFOLD_TAC_P k THEN HROW_CASES_TAC_P (HROW_INR_TM_P k) THENL
   [X86_STEPS_TAC ex (8--9) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[(HROW_JNE_P ()); (HROW_ADDG2_EQ0_P ()); VAL_EQ_0; WORD_SUB_0]) THEN
    HROW_DECIDE_TAC_P (mk_neg(HROW_H_TM_P k)) (HROW_HINT_INR_TAC_P ()) THEN
    (HROW_DROP_UNFOLD_TAC_P ()) THEN
    HROW_CASES_TAC_P (HROW_H_TM_P k) THENL
     [(if c.hr_late then X86_STEPS_TAC ex [10] else ALL_TAC) THEN
      HROW_HINT_PATH_TAC_P ex k (1 - late) (10 + late);
      HROW_LOOPTEST_TAC_P ex k 10];
    HROW_HINT_OUT_TAC_P k THEN (HROW_DROP_UNFOLD_TAC_P ()) THEN
    HROW_HINT_PATH_TAC_P ex k (1 - late) 8];;

(*** After the loop: the store of the count, or the rejection ***)

let HROW_EXIT_TAC_P c ex =
  let k = c.hr_k in
  let cntok = subst [mk_small_numeral(256 * (k + 1)),`P1:num`]
    `mld_hint_count (mld_polyvec_make_hint_32 x b) P1 <= 80` in
  REWRITE_TAC[] THEN HROW_CASES_TAC_P cntok THEN ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    FULL_INIT_TAC THEN X86_STEPS_TAC ex (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(REWRITE_TAC[(HROW_VAL_BYTE_P ())] THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let HROW_TAC_P c =
  let ex = HROW_EXEC_P c and k = c.hr_k in
  let p0 = mk_small_numeral(256 * k) and p1 = mk_small_numeral(256 * (k + 1)) in
  let pcn off = mk_binop `(+):num->num->num` `pc:num`
                  (mk_small_numeral(layout c.hr_fn + off)) in
  CONCRETIZE_F_EVENTS_TAC (HROW_TEMPLATE_P c) THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `x:num->int32`; `b:num->byte`;
                       `sig:int64`; `rsp0:int64`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst ex] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`mld_polyvec_make_hint_32 x b`; `80`; p1] GLUE_HINT_STEPS) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC (mk_binop `(-):num->num->num` (HROW_STEPS_TM_P k) p0)
   (pcn c.hr_head)
   (mk_cond(subst [p1,`P1:num`] `mld_hint_count (mld_polyvec_make_hint_32 x b) P1 <= 80`,
            pcn c.hr_store, pcn c.hr_rej))
   (HROW_INV_P c) THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(SPECL [`mld_polyvec_make_hint_32 x b`; `80`; p0; p1] (HROW_STEPS_POS_P ())) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ARITH_TAC];
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    HROW_BODY_TAC_P c ex;
    HROW_EXIT_TAC_P c ex];;

let PROVE_HROW_P c = prove(HROW_STMT_P c, HROW_TAC_P c);;

let parse_term = si_parse_term;;

(* ------------------------------------------------------------------------- *)
(* The instances with other registers. With the identity map they state the *)
(* lemmas of the originals.                                                  *)
(* ------------------------------------------------------------------------- *)

(* PWMLOOPG with the constant q^-1 2^32 in register q *)
let PWMLOOPQ_STMT q fn loop exit dx dy r0 =
  SI_WITH_REGS ["R12",q] (fun () -> PWMLOOPG_STMT_R fn loop exit dx dy r0);;
let PROVE_PWMLOOPQ q fn loop exit dx dy r0 =
  SI_WITH_REGS ["R12",q] (fun () -> PROVE_PWMLOOPG_R fn loop exit dx dy r0);;

(* T0U with the registers renamed by m *)
let T0UR_STMT m fn loop exit ob =
  SI_WITH_REGS m (fun () -> T0U_STMT_R fn loop exit ob);;
let PROVE_T0UR m fn loop exit ob =
  SI_WITH_REGS m (fun () -> PROVE_T0U_R fn loop exit ob);;

(* REDLOOPB, SUBLOOPB, ADDLOOPB with the row of w at register b *)
let REDLOOPBR_STMT b fn loop exit =
  SI_WITH_REGS ["RBX",b] (fun () -> REDLOOPB_STMT_R fn loop exit);;
let PROVE_REDLOOPBR b fn loop exit =
  SI_WITH_REGS ["RBX",b] (fun () -> PROVE_REDLOOPB_R fn loop exit);;
let SUBLOOPBR_STMT b fn loop exit yb =
  SI_WITH_REGS ["RBX",b] (fun () -> SUBLOOPB_STMT_R fn loop exit yb);;
let PROVE_SUBLOOPBR b fn loop exit yb =
  SI_WITH_REGS ["RBX",b] (fun () -> PROVE_SUBLOOPB_R fn loop exit yb);;
let ADDLOOPBR_STMT b fn loop exit xb =
  SI_WITH_REGS ["RBX",b] (fun () -> ADDLOOPB_STMT_R fn loop exit xb);;
let PROVE_ADDLOOPBR b fn loop exit xb =
  SI_WITH_REGS ["RBX",b] (fun () -> PROVE_ADDLOOPB_R fn loop exit xb);;

(* HROW for gamma2 = (q - 1) / 32 with the parameters of ML-DSA-65 or -87:
   omega, K, the offset of the hints in the signature, the packed w1 and the
   slots of the frame *)

type hrow_pset =
 { hp_w0 : int; hp_cb : int; hp_sigs : int; hp_map : (string*string) list };;

let HROW32_PSET omega k sigh w0 w1u sigs sighs =
  { hp_w0 = w0; hp_cb = sigh + omega; hp_sigs = sigs;
    hp_map = ["80",string_of_int omega; "84",string_of_int (omega + k);
              "2336",string_of_int sigh; "800",string_of_int w1u;
              "24",string_of_int sighs; "95232","261888"; "190464","523776";
              "4294872064","4294705408"] };;

let HROW65_PSET = HROW32_PSET 55 6 3248 0x1500 0x220 0x8 0x10;;
let HROW87_PSET = HROW32_PSET 75 8 4544 0x1a20 0x340 0x20 0x28;;

let SI_WITH_HROW ps f =
  hr_w0 () := ps.hp_w0; hr_wb () := 128; hr_cb () := ps.hp_cb; hr_sigs () := ps.hp_sigs;
  SI_WITH_REGS ps.hp_map f;;

let HROW32_STMT ps c = SI_WITH_HROW ps (fun () -> HROW_STMT_P c);;
let PROVE_HROW32 ps c = SI_WITH_HROW ps (fun () -> PROVE_HROW_P c);;

(* ------------------------------------------------------------------------- *)
(* G1AV: G1A (inline_attempt.ml) with the slot of the pointer to rho'' at    *)
(* rsp0 + rps and of kappa at rsp0 + rps + 8 (128 and 136 in G1A), and, if   *)
(* x4, for the code that zeroes the state from XMM4 (zero at the start)      *)
(* instead of XORPS XMM0 before the stores: one instruction less.            *)
(* ------------------------------------------------------------------------- *)

let g1av_sub c rps x4 s =
  subst_tokens ["@RPS@",string_of_int rps; "@KAPS@",string_of_int (rps + 8);
                "@X4@",(if x4 then "read XMM4 s = word 0 /\\" else "")]
               (g1a_sub c s);;

let G1AV_STMT c rps x4 = parse_term(g1av_sub c rps x4
 "exists f_events.
    forall e (rsp0:int64) (rp:int64) (R:num) kap j pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 16 rsp0 /\\ j < 65536 /\\
      ALL (nonoverlapping (rp,64))
        [(word_add rsp0 (word @ST@),204); (word_add rsp0 (word @IN@),66);
         (word_add rsp0 (word @JSLOT@),@JLEN@)] /\\
      ALL (nonoverlapping (word pc,libmldsa_size))
        [(word_add rsp0 (word @ST@),204); (word_add rsp0 (word @IN@),66);
         (word_add rsp0 (word @JSLOT@),@JLEN@)]
      ==> ensures x86
           (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + @FN@_@START@) /\\
                read RSP s = rsp0 /\\ read @JREG@ s = word j /\\ @X4@
                read (memory :> bytes64 (word_add rsp0 (word @RPS@))) s = rp /\\
                read (memory :> bytes16 (word_add rsp0 (word @KAPS@))) s = word kap /\\
                read (memory :> bytes(rp,64)) s = R /\\
                read events s = e)
           (\\s. read RIP s = word (pc + @FN@_@END@) /\\
                read RSP s = rsp0 /\\
                read @POS@ s = word 136 /\\ read @REM@ s = word 680 /\\
                read @OFF@ s = word 0 /\\
                read (memory :> @JSAVE@ (word_add rsp0 (word @JSLOT@))) s = @JVAL@ /\\
                read (memory :> bytes(word_add rsp0 (word @ST@),200)) s =
                  val(mld_keccak_absorb_once 136 0x1F 66
                       (R + 2 EXP 512 * val(word(kap + j):int16))) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events rsp0 rp pc /\\
                   memaccess_inbounds e2
                    [rp,64; word_add rsp0 (word @RPS@),10; word_add rsp0 (word @ST@),204;
                     word_add rsp0 (word @IN@),80]
                    [word_add rsp0 (word @ST@),204; word_add rsp0 (word @IN@),66;
                     word_add rsp0 (word @JSLOT@),@JLEN@]))
           (MAYCHANGE [RIP; RAX; RCX; @POS@; @REM@; @OFF@] ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4] ,, MAYCHANGE SOME_FLAGS ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(word_add rsp0 (word @ST@),204);
                       memory :> bytes(word_add rsp0 (word @IN@),66);
                       memory :> bytes(word_add rsp0 (word @JSLOT@),@JLEN@)])");;

let G1AV_TAC c x4 =
  let d = if x4 then 1 else 0 in
  let x4tm = `word_subword (ymm4_init:int256) (0,128):int128 = word 0` in
  let X4INIT_TAC =
    if not x4 then ALL_TAC else
    SUBGOAL_THEN x4tm ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th ->
        can (term_match [] `read XMM4 s = x:int128`) (concl th))) THEN
      ASM_REWRITE_TAC[XMM4; READ_COMPONENT_COMPOSE; READ_ZEROTOP_128] THEN
      CONV_TAC WORD_BLAST;
      ALL_TAC] in
  let X4RW_TAC =
    if not x4 then ALL_TAC else
    RULE_ASSUM_TAC(fun th -> if concl th = x4tm then th
                             else REWRITE_RULE[ASSUME x4tm] th) in
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [layout (c.ga_fn ^ "_" ^ c.ga_start), layout (c.ga_fn ^ "_" ^ c.ga_end)] in
  let st = c.ga_st and inb = c.ga_inb in
  let al k = parse_term(Printf.sprintf "aligned 16 (word_add rsp0 (word %d):int64)" k) in
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (rp:int64) (pc:num). f_ev_a rsp0 rp pc:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `rp:int64`; `R:num`;
                       `kap:num`; `j:num`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun n -> GHOST_INTRO_TAC (mk_var(Printf.sprintf "ymm%d_init" n,`:int256`))
                       (parse_term(Printf.sprintf "read YMM%d" n))) [0;1;2;3;4] THEN
  FULL_INIT_TAC THEN X4INIT_TAC THEN
  SUBGOAL_THEN `R < 2 EXP 512` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rp:int64`; `64`; `read memory (s0:x86state)`] READ_BYTES_BOUND) THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes(rp,64)) s = R`) (concl th)
    then MP_TAC(MATCH_MP (SPEC `4` MLD_READ_BYTES_CHUNKS)
                 (REWRITE_RULE[ARITH_RULE `64 = 16 * 4`] th))
    else NO_TAC) THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  REWRITE_TAC[EXP; DIV_1; WORD_ADD_0] THEN
  MAP_EVERY (fun k -> REWRITE_TAC[MP (SPECL [`R:num`; mk_small_numeral k] G1A_SUBW128)
      (CONJ (ASSUME `R < 2 EXP 512`) (EQT_ELIM(NUM_REDUCE_CONV(mk_binary "<" (mk_small_numeral k,`4`)))))
      |> CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC REWRITE_CONV[EXP; DIV_1])]) [0;1;2;3] THEN
  STRIP_TAC THEN
  MAP_EVERY (fun k -> SUBGOAL_THEN (al k) ASSUME_TAC THENL
      [MATCH_MP_TAC ALIGNED_WORD_ADD THEN ASM_REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
       CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUMBER_RULE; ALL_TAC])
    (map (fun i -> inb + 16 * i) (0--4) @ map (fun i -> st + 16 * i) (0--11)) THEN
  VERIF_SSE_STEPS_TAC exec (1--(26-d)) THEN X4RW_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[G1A_NONCE16; G1A_NONCE16B]) THEN
  G1A_ZBYTES_TAC (Printf.sprintf "s%d" (26-d)) (st + 176) (0--11) THEN
  VERIF_SSE_STEPS_TAC exec ((27-d)--(27-d)) THEN X4RW_TAC THEN
  G1A_ZBYTES_TAC (Printf.sprintf "s%d" (27-d)) (st + 64) (0--15) THEN
  G1A_ZBYTES_TAC (Printf.sprintf "s%d" (27-d)) (st + 128) (0--15) THEN
  G1A_ZBYTES_TAC (Printf.sprintf "s%d" (27-d)) (st + 188) (0--11) THEN
  VERIF_SSE_STEPS_TAC exec ((28-d)--(39-d)) THEN
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && lhs c = parse_term(Printf.sprintf
         "read (memory :> bytes16 (word_add rsp0 (word %d))) s%d" (inb + 64) (39-d))
    then X_CHOOSE_TAC `hjunk:112 word` (MATCH_MP G1A_LOW16 th) else NO_TAC) THEN
  VERIF_SSE_STEPS_TAC exec ((40-d)--(49-d)) THEN
  G1A_SPLIT16_TAC (Printf.sprintf "s%d" (49-d)) (st + 64) THEN
  G1A_CHAIN_TAC st (Printf.sprintf "s%d" (49-d)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[G1A_ZX_WORD32] THEN REPEAT CONJ_TAC THEN
  TRY(SUBGOAL_THEN `R + 2 EXP 512 * val(word(kap + j):int16) < 2 EXP 528` ASSUME_TAC THENL
       [MP_TAC(ISPEC `word(kap + j):int16` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_16] THEN
        UNDISCH_TAC `R < 2 EXP 512` THEN ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[G1A_S_WORD; G1A_M_JOIN; G1A_MODLEMMA] THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let PROVE_G1AV c rps x4 = prove(G1AV_STMT c rps x4, G1AV_TAC c x4);;
(* ------------------------------------------------------------------------- *)
(* SQZV: SQZ (inline_attempt.ml) for the code that keeps the pointer to the  *)
(* state in sp from before the loop (spre): mov sp, rdi instead of lea at   *)
(* the head, so one instruction less per iteration and the value of sp in   *)
(* the precondition and the invariant. ZERV: ZER with npre instructions     *)
(* before the call of memset (19 in ZER). The frame of SQZV reaches the end  *)
(* of the state or of the buffer, whichever is higher (SQZ assumes the       *)
(* buffer above the state).                                                  *)
(* ------------------------------------------------------------------------- *)

let sqzv_sub c spre s =
  sqz_sub c (subst_tokens
    ["@SPF@",(if spre then "read @SP@ s = word_add rsp0 (word @ST@) /\\ " else "");
     "@FRN@",string_of_int (296 + max (c.sq_buf + 680) (c.sq_st + 200))] s);;

let SQZV_STMT c spre = parse_term(sqzv_sub c spre
 "!mc ea el ev.
    memcpy_full_contract mc ea el ev
    ==> exists f_events.
      forall e (S:1600 word) (rsp0:int64) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        ALLPAIRS nonoverlapping [(word_sub rsp0 (word 296),@FRN@)]
          [(word pc,libmldsa_size); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures x86
          (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + @FN@_@HEAD@) /\\
                read RSP s = rsp0 /\\
                read @POS@ s = word 136 /\\ read @REM@ s = word 680 /\\
                read @OFF@ s = word 0 /\\
                @SPF@(read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes (word_add rsp0 (word @ST@),200)) s = val(S:1600 word) /\\
                read events s = e)
          (\\s. read RIP s = word (pc + @FN@_@EXIT@) /\\
                read RSP s = rsp0 /\\
                read @POS@ s = word 136 /\\ read @REM@ s = word 0 /\\
                read @OFF@ s = word 680 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes (word_add rsp0 (word @ST@),200)) s =
                  val(keccak_squeeze 5 S) /\\
                (!j. j < 680
                     ==> read (memory :> bytes8 (word_add rsp0 (word (@BUF@ + j)))) s =
                         mld_keccak_squeeze_byte 136 S 136 j) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events rsp0 mc pc /\\
                   memaccess_inbounds e2
                    [word_sub rsp0 (word 296),@FRN@; word(pc + got_memcpy),8; ea,el;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192]
                    [word_sub rsp0 (word 296),296; word_add rsp0 (word @ST@),200;
                     word_add rsp0 (word @BUF@),680]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [RSP] ,, MAYCHANGE [@POS@; @REM@; @OFF@; @LEN@; @SP@] ,,
           MAYCHANGE [memory :> bytes(word_sub rsp0 (word 296),296);
                      memory :> bytes(word_add rsp0 (word @ST@),200);
                      memory :> bytes(word_add rsp0 (word @BUF@),680)])");;

let SQZV_INV c spre = parse_term(sqzv_sub c spre
 "\\i s. read RSP s = rsp0 /\\ read @POS@ s = word 136 /\\
        read @REM@ s = word (680 - 136 * i) /\\ read @OFF@ s = word (136 * i) /\\ @SPF@
        (read DF s <=> false) /\\
        read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
        read (memory :> bytes(ea,el)) s = ev /\\
        read (memory :> bytes (word_add rsp0 (word @ST@),200)) s = val(keccak_squeeze i S) /\\
        read (memory :> bytes(word_add rsp0 (word @BUF@),136 * i)) s =
          nsum {j | j < i} (\\j. 2 EXP (8 * 136 * j) *
                                val(keccak_squeeze (j + 1) S) MOD 2 EXP (8 * 136))");;

let SQZV_TAC c spre =
  let d = if spre then 1 else 0 in
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [layout (c.sq_fn ^ "_" ^ c.sq_lo), layout (c.sq_fn ^ "_" ^ c.sq_exit);
      layout "plt_memcpy", layout "plt_memcpy" + 16] in
  let wb6 = parse_term(Printf.sprintf
    "read (memory :> wbytes (word_add rsp0 (word %d):int64)) s%d:1600 word" c.sq_st (6-d)) in
  let lbl n = parse_term(Printf.sprintf "pc + %s_%s" c.sq_fn n) in
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memcpy_full_contract] th) "H_MEMCPY") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   (SQZ_RENAME_E2 MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600) "H_PERM" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (mc:int64) (pc:num).
      APPEND (f_ev_epil rsp0 mc pc)
       (APPEND (ENUMERATEL 5 (\i. if i + 1 < 5 then f_ev_c rsp0 mc pc i else f_ev_l rsp0 mc pc i))
               (f_ev_prol rsp0 mc pc)):(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `S:1600 word`; `rsp0:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; ALLPAIRS; PAIRWISE;
              NONOVERLAPPING_CLAUSES; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `5` (lbl c.sq_head) (lbl c.sq_exit) (SQZV_INV c spre) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; CONJUNCT1 ENUMERATEL; CONJUNCT1 APPEND] THEN
    REPEAT CONJ_TAC THEN
    REWRITE_TAC[keccak_squeeze; NSUM_CLAUSES_NUMSEG_LT; READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
    TRY DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN FULL_INIT_TAC THEN
    X86_STEPS_TAC exec (1--(5-d)) THEN SQZ_NORM_TAC THEN
    KECCAK_STATE_WBYTES_TAC `keccak_squeeze i S` THEN
    FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc exec "H_PERM"
     [`read RDI s`; `keccak_squeeze i S`; `pc:num`; `read RSP s`;
      `read (memory :> bytes64 (read RSP s)) s`] SQZ_ALLOWED (6-d) THEN
    EXPAND_CALLEE_MEMACCESS_TAC THEN RSP_NORM_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[SQZ_SQ_SUC]) THEN SQZ_NORM_TAC THEN
    FIRST_X_ASSUM(fun th ->
      if (try lhs(concl th) = wb6 with _ -> false)
      then ASSUME_TAC(MATCH_MP SQZ_FIRST136 th) THEN ASSUME_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600] th)
      else NO_TAC) THEN
    X86_STEPS_TAC exec ((7-d)--(16-d)) THEN SQZ_NORM_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `i:num` SQZ_CSEL) (ASSUME `i < 5`)]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `i:num` SQZ_VAL136) (ASSUME `i < 5`); MULT_CLAUSES]) THEN
    SQZ_NORM_TAC THEN
    LIBC_PLT_TAC exec (layout "plt_memcpy") (layout "got_memcpy") (16-d) THEN
    SQZ_LIBC_CALL_TAC "H_MEMCPY" exec
     [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
      `val(keccak_squeeze (i + 1) S) MOD 2 EXP (8 * 136)`;
      `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`] SQZ_ALLOWED (18-d) THEN
    EXPAND_CALLEE_MEMACCESS_TAC THEN RSP_NORM_TAC THEN SQZ_NORM_TAC THEN
    X86_STEPS_TAC exec ((19-d)--(22-d)) THEN SQZ_NORM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `i:num` SQZ_ARITH) (ASSUME `i < 5`)]) THEN
    REWRITE_TAC[MP (SPEC `i:num` SQZ_ARITH) (ASSUME `i < 5`)] THEN SQZ_NORM_TAC THEN
    ASM_CASES_TAC `i + 1 < 5` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    FIRST [MATCH_MP_TAC SQZ_EXTBLK THEN ASM_REWRITE_TAC[];
           SQZ_MAYCHANGE_TAC;
           REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
           ASM_REWRITE_TAC[] THEN SQZ_SAFETY_TAC];
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `136 * 5 = 680`]) THEN
    CONJ_TAC THENL
     [MP_TAC(REWRITE_RULE[ARITH_RULE `136 * 5 = 680`]
        (SPECL [parse_term(Printf.sprintf "word_add rsp0 (word %d):int64" c.sq_buf);
                `136`; `5`; `S:1600 word`; `s0:x86state`] MLD_SQUEEZE_BLOCKS_BYTES8)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[ARITH_RULE `0 < 136`]; ALL_TAC] THEN
      REWRITE_TAC[WORD_ADD_ASSOC_CONSTS; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      DISCH_THEN ACCEPT_TAC;
      ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;


let PROVE_SQZV c spre = prove(SQZV_STMT c spre, SQZV_TAC c spre);;


let ZERV_TAC c npre =
  let fstart = layout (c.zr_fn ^ "_" ^ c.zr_start) in
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [fstart, layout c.zr_fn + c.zr_fin; layout "plt_memset", layout "plt_memset" + 16] in
  let al k = parse_term(Printf.sprintf "aligned 16 (word_add rsp0 (word %d):int64)" k) in
  let allowed = ref [`rsp0:int64`; `pc:num`; `mf:int64`] in
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] th) "H_MEMSET") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (mf:int64) (pc:num). f_ev_z rsp0 mf pc:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; ALLPAIRS; PAIRWISE;
              NONOVERLAPPING_CLAUSES; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun k -> SUBGOAL_THEN (al k) ASSUME_TAC THENL
      [MATCH_MP_TAC ALIGNED_WORD_ADD THEN ASM_REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
       CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUMBER_RULE; ALL_TAC])
    (map (fun i -> c.zr_st + 16 * i) (0--12) @ map (fun i -> c.zr_inb + 16 * i) (0--3)) THEN
  GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
  FULL_INIT_TAC THEN
  VERIF_SSE_STEPS_TAC exec (1--npre) THEN
  SUBGOAL_THEN (parse_term(Printf.sprintf
    "nonoverlapping (word_add rsp0 (word %d):int64,680) (word_sub rsp0 (word 8),8)" c.zr_buf))
   ASSUME_TAC THENL
   [REWRITE_TAC[WORD_RULE `word_sub (x:int64) y = word_add x (word_neg y)`] THEN
    CONV_TAC WORD_REDUCE_CONV THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  X86_STEPS_TAC exec ((npre+1)--(npre+1)) THEN
  LIBC_PLT_TAC exec (layout "plt_memset") (layout "got_memset") (npre+1) THEN
  LIBC_FULL_CALL_TAC "H_MEMSET" exec
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
    `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   allowed (npre+3) THEN
  RSP_NORM_TAC THEN
  YMM_GHOST_TAC (mk_var(Printf.sprintf "s%d" (npre+3),`:x86state`)) ["YMM0","ymm0_mid"; "YMM5","ymm5_mid"] THEN
  VERIF_SSE_STEPS_TAC exec ((npre+4)--(npre+3+c.zr_post)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;


let PROVE_ZERV c npre = prove(ZER_STMT c, ZERV_TAC c npre);;


(* ------------------------------------------------------------------------- *)
(* mld_polyz_pack_19 (gamma1 = 2^19, ML-DSA-65/87) of z at rsp0 + ob, read   *)
(* as [rsp + rcx * 8 + ob] and + 4, RCX = i: 128 iterations of 2            *)
(* coefficients into 5 bytes, stored at RAX - 3 (16 bits), RAX - 1 (8 bits)  *)
(* and RAX (16 bits), RAX being op + 3 + 5 i.                                *)
(* ------------------------------------------------------------------------- *)

let ZPACK19_ALIASES =
  ["word_add (word_add op (word (5 * i + 3))) (word 18446744073709551613):int64 = word_add op (word (5 * i))";
   "word_add (word_add op (word (5 * i + 3))) (word 18446744073709551615):int64 = word_add op (word (5 * i + 2))"];;

let ZPACK19_TEST = prove
 (`!i. i < 128
       ==> (val(word(i + 18446744073709551489):int64) = 0 <=> ~(i + 1 < 128))`,
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC NUM_REDUCE_CONV);;

let ZPACK19_STMT fn loop exit ob =
  parse_term(Printf.sprintf
  "exists f_events.
  forall e rsp0 op pc (z:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    ALL (nonoverlapping (op,640)) [(word_add rsp0 (word %d),1024); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word_add op (word 3) /\\ read RCX s = word 0 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = z i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word_add op (word 643) /\\ read RCX s = word 128 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = z i) /\\
              (!j. j < 640 ==> read (memory :> bytes8 (word_add op (word j))) s =
                               mld_polyz_pack_19 z j) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 op pc /\\
                 memaccess_inbounds e2 [word_add rsp0 (word %d),1024; op,640] [op,640]))
         (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; RDI] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(op,640)])"
  ob image_mc fn loop ob fn exit ob ob);;

let ZPACK19_TAC exec fn loop exit ob =
  let lth = ZPACK19_TEST in
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (op:int64) (pc:num).
      APPEND (f_ev_epil rsp0 op pc)
       (APPEND (ENUMERATEL 128 (\i. f_ev_loop rsp0 op pc i)) (f_ev_prol rsp0 op pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `op:int64`; `pc:num`; `z:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `128` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read RSP s = rsp0 /\\ read RAX s = word_add op (word (5 * i + 3)) /\\
          read RCX s = word i /\\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = z j) /\\
          (!j. j < 5 * i
               ==> read(memory :> bytes8(word_add op (word j))) s = mld_polyz_pack_19 z j)" ob)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    VAL_INT64_TAC `i:num` THEN
    SUBGOAL_THEN (parse_term(Printf.sprintf
      "!k. k < 2 ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * (2 * i + k))))) s0 = (z:num->int32)(2 * i + k)" ob))
      MP_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    STRIP_TAC THEN ADDR_LINEAR_BASES_TAC [ob] THEN
    ALT_SIM_TAC
     (map (fun (c,t) -> (parse_term c, parse_term t))
        [Printf.sprintf "%d + 8 * i" ob, Printf.sprintf "8 * i + %d" ob;
         Printf.sprintf "%d + (8 * i + 4)" ob, Printf.sprintf "8 * i + %d" (ob + 4)]) THEN
    ALIAS_ASSUME_TAC ZPACK19_ALIASES THEN
    X86_STEPS_TAC exec (1--16) THEN
    ZPACK_SPLIT16_TAC "s16" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `i:num` lth) (ASSUME `i < 128`); ADD_CLAUSES;
                                G1A_ZX_MOD16; G1A_ZX_MOD8]) THEN
    ADDR_NORMALIZE_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    LOOP_TEST_TAC THEN PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(REWRITE_TAC[ARITH_RULE `5 * (i + 1) + 3 = 5 * i + 8`] THEN
        CONV_TAC WORD_RULE THEN NO_TAC) THEN
    TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(REWRITE_TAC[CHUNK_OUTPUT_SPLIT_N 5] THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC EXPAND_CASES_CONV THEN
        REWRITE_TAC[mld_polyz_pack_19] THEN
        SIMP_TAC[DIVMOD_CHUNK; ARITH] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[ADD_CLAUSES; LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
        REWRITE_TAC[ADD_CLAUSES; WORD_ADD_0] THEN
        ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THEN APP_BLAST_TAC `z:num->int32` THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    FULL_EXIT0_TAC];;

let PROVE_ZPACK19 fn loop exit ob =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(ZPACK19_STMT fn loop exit ob, ZPACK19_TAC exec fn loop exit ob);;

(* ------------------------------------------------------------------------- *)
(* mld_polyeta_unpack_4 (eta = 4, ML-DSA-65) of the 128 bytes b at a = RAX, *)
(* read as [rax + rcx], RCX = i: 128 iterations of one byte into two        *)
(* coefficients 4 - (b & 15) and 4 - (b >> 4), stored at [rsp + rcx * 8 +   *)
(* ob] (twice: the low nibble first) and + 4.                                *)
(* ------------------------------------------------------------------------- *)

let ETA4U_LANES = prove
 (`!(b:num->byte) i.
     mld_polyeta_unpack_4 b (2 * i) =
     word_sub (word 4) (word_and (word_zx (b i)) (word 15)) /\
     mld_polyeta_unpack_4 b (2 * i + 1) =
     word_sub (word 4) (word_ushr (word_zx (b i)) 4)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_polyeta_unpack_4] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[REWRITE_RULE[ADD_CLAUSES]
               (MP (SPECL [`2`; `i:num`; `0`] DIVMOD_CHUNK) (ARITH_RULE `0 < 2`));
              MP (SPECL [`2`; `i:num`; `1`] DIVMOD_CHUNK) (ARITH_RULE `1 < 2`)] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let ETA4U_TEST = prove
 (`!i. i < 128
       ==> (val(word_add (word i) (word 18446744073709551489):int64) = 0 <=>
            ~(i + 1 < 128))`,
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC NUM_REDUCE_CONV);;

let ETA4U_STMT fn loop exit ob =
  parse_term(Printf.sprintf
  "exists f_events.
  forall e a rsp0 pc (b:num->byte).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    ALL (nonoverlapping (word_add rsp0 (word %d),1024))
        [(a,128); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = a /\\ read RCX s = word 0 /\\
              (!j. j < 128 ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = a /\\ read RCX s = word 128 /\\
              (!j. j < 128 ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s =
                               mld_polyeta_unpack_4 b i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events a rsp0 pc /\\
                 memaccess_inbounds e2 [a,128; word_add rsp0 (word %d),1024]
                                       [word_add rsp0 (word %d),1024]))
         (MAYCHANGE [RIP; RCX; RDX; RSI; RDI] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(word_add rsp0 (word %d),1024)])"
  ob image_mc fn loop fn exit ob ob ob ob);;

let ETA4U_TAC exec fn loop exit ob =
  let obt = mk_small_numeral ob in
  let arith1 = ARITH_RULE(subst [obt,`ob:num`] `ob + 4 * (2 * i + 0) = ob + 8 * i`)
  and arith2 = ARITH_RULE(subst [obt,`ob:num`]
                 `ob + 4 * (2 * i + 1) = ob + (8 * i + 4)`) in
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (rsp0:int64) (pc:num).
      APPEND (f_ev_epil a rsp0 pc)
       (APPEND (ENUMERATEL 128 (\i. f_ev_loop a rsp0 pc i)) (f_ev_prol a rsp0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `rsp0:int64`; `pc:num`; `b:num->byte`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `128` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read RSP s = rsp0 /\\ read RAX s = a /\\ read RCX s = word i /\\
          (!j. j < 128 ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\\
          (!j. j < 2 * i
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s =
                   mld_polyeta_unpack_4 b j)" ob)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0; ADD_CLAUSES] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    VAL_INT64_TAC `i:num` THEN
    SUBGOAL_THEN `read(memory :> bytes8(word_add a (word i))) s0 = (b:num->byte) i`
      ASSUME_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read(memory :> bytes8(word_add a (word (1 * i)))) s0 = (b:num->byte) i`
      ASSUME_TAC THENL
     [ASM_REWRITE_TAC[MULT_CLAUSES]; ALL_TAC] THEN
    X86_STEPS_TAC exec (1--14) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `i:num` ETA4U_TEST) (ASSUME `i < 128`)]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
    ADDR_MUL1_TAC ob THEN ADDR_NORMALIZE_TAC THEN ADDR_MUL1_TAC ob THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
    TRY(REWRITE_TAC[CHUNK_OUTPUT_SPLIT_N 2] THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC EXPAND_CASES_CONV THEN
        REWRITE_TAC[arith1; arith2; ADD_CLAUSES] THEN
        REWRITE_TAC[REWRITE_RULE[ADD_CLAUSES] ETA4U_LANES; ETA4U_LANES] THEN
        ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THEN APP_BLAST_TAC `b:num->byte` THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    FULL_EXIT0_TAC];;

let PROVE_ETA4U fn loop exit ob =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(ETA4U_STMT fn loop exit ob, ETA4U_TAC exec fn loop exit ob);;

(* ------------------------------------------------------------------------- *)
(* mld_poly_decompose with gamma2 = (q - 1) / 32 (ML-DSA-65 and ML-DSA-87),  *)
(* one coefficient per iteration, as DECOMP88 (inline_attempt.ml): the low   *)
(* part a0 replaces a, the high part a1 is stored at rsp0 + w1b, at          *)
(* [rsp + idx * 4 + w1d] (w1b = w1d + 4 r0), idx running from r0 to r0 +     *)
(* 256. The polynomial is read either from the stack ([rsp + idx * 4 + wd],  *)
(* at rsp0 + wb, wb = wd + 4 r0: dc_wd = Some wd), as in the unrolled rows   *)
(* of 65, or through the pointer a in the register dc_wreg ([reg + idx * 4], *)
(* r0 = 0: dc_wd = None), as in the rolled row loop of 87. dc_val, dc_hi and *)
(* dc_lo are the registers of a, of a1 (and of the product a1 * -2 gamma2)  *)
(* and of a0; dc_regs those the loop changes besides RIP.                    *)
(* ------------------------------------------------------------------------- *)

type dc_cfg =
  {dc_fn: string; dc_loop: string; dc_exit: string; dc_idx: string; dc_r0: int;
   dc_wd: int option; dc_wreg: string; dc_w1d: int;
   dc_val: string; dc_hi: string; dc_lo: string; dc_regs: string};;

let dc_wb c = match c.dc_wd with Some wd -> wd + 4 * c.dc_r0 | None -> 0;;
let dc_w1b c = c.dc_w1d + 4 * c.dc_r0;;

(* the address of coefficient j of the polynomial, its region, and the
   variables of the statement *)
let dc_waddr c j = match c.dc_wd with
    Some _ -> Printf.sprintf "word_add rsp0 (word (%d + 4 * %s))" (dc_wb c) j
  | None -> Printf.sprintf "word_add a (word (4 * %s))" j;;
let dc_wreg c = match c.dc_wd with
    Some _ -> Printf.sprintf "word_add rsp0 (word %d)" (dc_wb c)
  | None -> "a";;

let dc_sub c s =
  subst_tokens
   ["@FN@",c.dc_fn; "@MC@",image_mc; "@LOOP@",c.dc_loop; "@EXIT@",c.dc_exit;
    "@IDX@",c.dc_idx; "@R0@",string_of_int c.dc_r0;
    "@R1@",string_of_int (c.dc_r0 + 256); "@W@",dc_wreg c;
    "@W1B@",string_of_int (dc_w1b c); "@REGS@",c.dc_regs;
    "@AV@",(match c.dc_wd with Some _ -> "" | None -> "a");
    "@APRE@",(match c.dc_wd with Some _ -> ""
              | None -> Printf.sprintf "read %s s = a /\\" c.dc_wreg);
    "@WI@",dc_waddr c "i"; "@WJ@",dc_waddr c "j"] s;;

let DECOMP32_STMT c = parse_term(dc_sub c
  "exists f_events.
  forall e @AV@ rsp0 pc (x:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    PAIRWISE nonoverlapping
     [(@W@,1024); (word_add rsp0 (word @W1B@),1024); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) @MC@ /\\
              read RIP s = word (pc + @FN@_@LOOP@) /\\
              read RSP s = rsp0 /\\ @APRE@ read @IDX@ s = word @R0@ /\\
              (!i. i < 256 ==> read (memory :> bytes32 (@WI@)) s = x i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + @FN@_@EXIT@) /\\
              read RSP s = rsp0 /\\ @APRE@ read @IDX@ s = word @R1@ /\\
              (!i. i < 256 ==> read (memory :> bytes32 (@WI@)) s =
                               mld_poly_decompose_lo_32 x i) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (@W1B@ + 4*i)))) s =
                               mld_poly_decompose_hi_32 x i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events @AV@ rsp0 pc /\\
                 memaccess_inbounds e2 [@W@,1024; word_add rsp0 (word @W1B@),1024]
                                       [@W@,1024; word_add rsp0 (word @W1B@),1024]))
         (MAYCHANGE [RIP; @REGS@] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes(@W@,1024);
                     memory :> bytes(word_add rsp0 (word @W1B@),1024)])");;

(* a0 = a + a1 * (-2 gamma2), then a0 - q if (q - 1) / 2 - a0 < 0, with the
   product generalized before the bit-blasting (DECOMPOSE_LO_32_CLANG of
   inline_verify65.ml) *)
let DECOMP_LO32_LANE_TAC (reg:term) (v:term) =
  FIRST_X_ASSUM(fun th ->
    let l,r = dest_eq(concl th) in
    if (try rand(rator l) = reg with Failure _ -> false) &&
       is_comb r && rator r = `word_zx:int32->int64` && free_in v r then
      let t = rand r and y = genvar(type_of v) in
      let ty = subst[y,v] t in
      let lemma = prove
       (mk_forall(y,mk_eq(ty,mk_comb(`mld_decompose_lo_32`,y))),
        GEN_TAC THEN REWRITE_TAC[DECOMPOSE_LO_32_CLANG; mld_ct_sel; mld_ct_cmask_neg] THEN
        CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
        REWRITE_TAC[MULT_CLAUSES; WORD_VAL; WORD_ZX_ZX_32_64_32] THEN
        SPEC_TAC(mk_comb(mk_comb(`word_mul:int32->int32->int32`,mk_comb(`mld_decompose_hi_32`,y)),
                         `word 4294443520:int32`),`p:int32`) THEN
        GEN_TAC THEN BITBLAST_TAC) in
      ASSUME_TAC th THEN RULE_ASSUM_TAC(REWRITE_RULE[lemma])
    else NO_TAC);;

let DECOMP32_TAC exec c =
  let wb = dc_wb c and w1b = dc_w1b c in
  let idx = idx_expr c.dc_r0 1 in
  let alias d b =
    if d >= 0 then ALL_TAC else
    ALIAS_ASSUME_TAC
     [Printf.sprintf "word_add rsp0 (word (4 * (%s) + %s)):int64 = word_add rsp0 (word (%d + 4 * i))"
        idx (disp_num d) b] in
  let reg s = mk_const(s,[]) in
  let isrsp = c.dc_wd <> None in
  CONCRETIZE_F_EVENTS_TAC
   (if isrsp then
     `\(rsp0:int64) (pc:num).
      APPEND (f_ev_epil rsp0 pc)
       (APPEND (ENUMERATEL 256 (\i. f_ev_loop rsp0 pc i)) (f_ev_prol rsp0 pc))
      :(uarch_event)list`
    else
     `\(a:int64) (rsp0:int64) (pc:num).
      APPEND (f_ev_epil a rsp0 pc)
       (APPEND (ENUMERATEL 256 (\i. f_ev_loop a rsp0 pc i)) (f_ev_prol a rsp0 pc))
      :(uarch_event)list`) THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   ([`e:(uarch_event)list`] @ (if isrsp then [] else [`a:int64`]) @
    [`rsp0:int64`; `pc:num`; `x:num->int32`]) THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; PAIRWISE; ALL; fst exec;
              mld_poly_decompose_lo_32; mld_poly_decompose_hi_32] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256` (parse_term(dc_sub c "pc + @FN@_@LOOP@"))
   (parse_term(dc_sub c "pc + @FN@_@EXIT@"))
   (parse_term(dc_sub c (Printf.sprintf
   "\\i s. read RSP s = rsp0 /\\ @APRE@
          read @IDX@ s = word (%s) /\\
          (!j. i <= j /\\ j < 256
               ==> read(memory :> bytes32(@WJ@)) s = x j) /\\
          (!j. j < i
               ==> read(memory :> bytes32(@WJ@)) s =
                   mld_decompose_lo_32 (x j)) /\\
          (!j. j < i
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s =
                   mld_decompose_hi_32 (x j))" idx w1b))) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ONE_INPUT_SPLIT] o
      check (fun th -> is_forall(concl th) &&
        free_in `x:num->int32` (concl th) &&
        not(free_in `mld_decompose_lo_32` (concl th)) &&
        not(free_in `mld_decompose_hi_32` (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    VAL_INT64_TAC (parse_term idx) THEN
    (match c.dc_wd with
       Some wd ->
         ASSUME_TAC(REWRITE_RULE[ARITH_RULE (parse_term(Printf.sprintf "%d + 4 * i = 4 * (%s) + %d" wb idx wd))]
           (ASSUME (parse_term(Printf.sprintf "read(memory :> bytes32(word_add rsp0 (word(%d + 4 * i)))) s0 = (x:num->int32) i" wb)))) THEN
         alias wd wb
     | None -> ALL_TAC) THEN
    alias c.dc_w1d w1b THEN
    X86_STEPS_TAC exec (1--9) THEN
    REG32_LANE_TAC (reg c.dc_hi) `(x:num->int32) i` `mld_decompose_hi_32` [DECOMPOSE_HI_32_ALT] THEN
    X86_STEPS_TAC exec (10--22) THEN
    DECOMP_LO32_LANE_TAC (reg c.dc_lo) `(x:num->int32) i` THEN
    X86_STEPS_TAC exec (23--26) THEN
    ADDR_LINEAR_BASES_TAC (if isrsp then [wb; w1b] else [w1b]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ONE_OUTPUT_SPLIT] THEN
    LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
    TRY(REWRITE_TAC[WORD_ZX_ZX_32_64_32] THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    FULL_EXIT0_TAC];;

let PROVE_DECOMP32 c =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (c.dc_fn^"_"^c.dc_loop), layout (c.dc_fn^"_"^c.dc_exit))] in
  prove(DECOMP32_STMT c, DECOMP32_TAC exec c);;

(* ------------------------------------------------------------------------- *)
(* mld_polyw1_pack_32 (4 bits per coefficient) of the high parts x at rsp0 + *)
(* ib, as W1PACK32 (inline_verify65.ml): 16 iterations, each loading 16      *)
(* coefficients by four MOVAPS from [rsp + idx * 8 + ib - 8 r0], idx being   *)
(* r0 + 8 i, and storing 8 bytes by two MOVD, the mask 0xff of each 32-bit  *)
(* lane in the register wp_mask (XMM6 in signing). The bytes go either to    *)
(* rsp0 + ob ([rsp + idx + ob - r0 - 4] and [.. + ob - r0], wp_ob = Some ob, *)
(* the unrolled rows of 65) or to op through the register wp_oreg = op + 4   *)
(* ([reg + idx - 4] and [reg + idx], r0 = 0, wp_ob = None, the rolled row    *)
(* loop of 87). The lemma starts at the setting of idx, wp_start (the label  *)
(* of the exit of the decomposition), two instructions before the loop.      *)
(* ------------------------------------------------------------------------- *)

type wp_cfg =
  {wp_fn: string; wp_start: string; wp_loop: string; wp_exit: string;
   wp_idx: string; wp_r0: int; wp_ib: int; wp_ob: int option; wp_oreg: string;
   wp_mask: string};;

let wp_mask_ymm c = "YMM" ^ String.sub c.wp_mask 3 (String.length c.wp_mask - 3);;

let wp_op c = match c.wp_ob with
    Some ob -> Printf.sprintf "word_add rsp0 (word %d)" ob | None -> "op";;
let wp_opj c j = match c.wp_ob with
    Some ob -> Printf.sprintf "word_add rsp0 (word (%d + %s))" ob j
  | None -> Printf.sprintf "word_add op (word %s)" j;;

let wp_sub c s =
  subst_tokens
   ["@FN@",c.wp_fn; "@MC@",image_mc; "@START@",c.wp_start; "@LOOP@",c.wp_loop;
    "@EXIT@",c.wp_exit; "@IDX@",c.wp_idx; "@R0@",string_of_int c.wp_r0;
    "@R1@",string_of_int (c.wp_r0 + 128);
    "@IX@",(if c.wp_r0 = 0 then "8 * i" else Printf.sprintf "%d + 8 * i" c.wp_r0); "@IB@",string_of_int c.wp_ib;
    "@OP@",wp_op c; "@OPJ@",wp_opj c "j"; "@MASK@",c.wp_mask;
    "@OPV@",(match c.wp_ob with Some _ -> "" | None -> "op");
    "@OPRE@",(match c.wp_ob with Some _ -> ""
              | None -> Printf.sprintf "read %s s = word_add op (word 4) /\\" c.wp_oreg)] s;;

let W1PACK4G_STMT c = parse_term(wp_sub c
  "exists f_events.
  forall e rsp0 @OPV@ pc (x:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    aligned 16 (word_add rsp0 (word @IB@)) /\\
    ALL (nonoverlapping (@OP@,128)) [(word_add rsp0 (word @IB@),1024); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) @MC@ /\\
              read RIP s = word (pc + @FN@_@START@) /\\
              read RSP s = rsp0 /\\ @OPRE@
              read @MASK@ s = word 0x000000ff000000ff000000ff000000ff /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (@IB@ + 4*i)))) s = x i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + @FN@_@EXIT@) /\\
              read RSP s = rsp0 /\\ read @IDX@ s = word @R1@ /\\ @OPRE@
              read @MASK@ s = word 0x000000ff000000ff000000ff000000ff /\\
              (!j. j < 128 ==> read (memory :> bytes8 (@OPJ@)) s = mld_polyw1_pack_32 x j) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 @OPV@ pc /\\
                 memaccess_inbounds e2 [word_add rsp0 (word @IB@),1024; @OP@,128] [@OP@,128]))
         (MAYCHANGE [RIP; @IDX@] ,, MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(@OP@,128)])");;

let W1P4_SETUP_TAC exec c =
  let isrsp = c.wp_ob <> None in
  CONCRETIZE_F_EVENTS_TAC
   (if isrsp then
     `\(rsp0:int64) (pc:num).
      APPEND (f_ev_epil rsp0 pc)
       (APPEND (ENUMERATEL 16 (\i. f_ev_loop rsp0 pc i)) (f_ev_prol rsp0 pc))
      :(uarch_event)list`
    else
     `\(rsp0:int64) (op:int64) (pc:num).
      APPEND (f_ev_epil rsp0 op pc)
       (APPEND (ENUMERATEL 16 (\i. f_ev_loop rsp0 op pc i)) (f_ev_prol rsp0 op pc))
      :(uarch_event)list`) THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   ([`e:(uarch_event)list`; `rsp0:int64`] @ (if isrsp then [] else [`op:int64`]) @
    [`pc:num`; `x:num->int32`]) THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `16` (parse_term(wp_sub c "pc + @FN@_@LOOP@"))
   (parse_term(wp_sub c "pc + @FN@_@EXIT@"))
   (parse_term(wp_sub c
   "\\i s. read RSP s = rsp0 /\\
          read @IDX@ s = word (@IX@) /\\ @OPRE@
          read @MASK@ s = word 0x000000ff000000ff000000ff000000ff /\\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add rsp0 (word(@IB@ + 4 * j)))) s = x j) /\\
          (!j. j < 8 * i
               ==> read(memory :> bytes8(@OPJ@)) s = mld_polyw1_pack_32 x j)"));;

let W1P4_PRE_TAC exec =
  FULL_INIT_TAC THEN X86_STEPS_TAC exec (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0; ADD_CLAUSES] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let W1P4_BODY_TAC exec c =
  let ib = c.wp_ib and r0 = c.wp_r0 in
  let d = ib - 8 * r0 in
  let ix = if r0 = 0 then "8 * i" else Printf.sprintf "%d + 8 * i" r0 in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
  GHOST_INTRO_TAC `ymm2_init:int256` `read YMM2` THEN
  GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN
  GHOST_INTRO_TAC `ymm4_init:int256` `read YMM4` THEN
  FULL_INIT_TAC THEN
  XMM_EXISTSTOP_TAC "topm" (mk_const(wp_mask_ymm c,[])) THEN
  VAL_INT64_TAC (parse_term ix) THEN
  MAP_EVERY (fun k -> ALIGN16_IDX_TAC `rsp0:int64`
      (parse_term(Printf.sprintf "8 * (%s) + %d" ix (d + k)))) [0; 16; 32; 48] THEN
  SUBGOAL_THEN (parse_term(Printf.sprintf "!k. k < 16 ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * (16 * i + k))))) s0 = (x:num->int32)(16 * i + k)" ib)) MP_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  STRIP_TAC THEN ADDR_LINEAR_BASES_TAC [ib] THEN
  MAP_EVERY (fun g ->
    MERGE_LIN_TAC_B 2 [ib]
      (parse_term(Printf.sprintf "read(memory :> bytes128(word_add rsp0 (word (8 * (%s) + %d)))) s0" ix (d + 16 * g))))
    [0;1;2;3] THEN
  (if c.wp_ob = None then ALIAS_ASSUME_TAC W1PACK32_ALIASES else ALL_TAC) THEN
  (fun g -> abbrev_ctr () := 0; ALL_TAC g) THEN
  ABBREV_YMM_STEPS_TAC exec (1--22) THEN X86_STEPS_TAC exec (23--25);;

let W1P4_FIN_TAC c =
  let abbr th = match concl th with
      Comb(Comb(Const("abbrev_def",_),_),_) -> true | _ -> false in
  let maskth = match c.wp_mask with "XMM5" -> XMM5 | "XMM6" -> XMM6 | "XMM7" -> XMM7
               | _ -> failwith "W1P4_FIN_TAC: mask register" in
  let stores = match c.wp_ob with
      Some ob -> [parse_term(Printf.sprintf "word_add rsp0 (word (%d + 8 * i)):int64" ob);
                  parse_term(Printf.sprintf "word_add rsp0 (word (%d + 8 * i + 4)):int64" ob)]
    | None -> [`word_add op (word (8 * i)):int64`; `word_add op (word (8 * i + 4)):int64`] in
  RULE_ASSUM_TAC(fun th -> if abbr th then REWRITE_RULE[PACKUSWB_JOIN; PACKUSWB_SAT_WORD] th
                           else th) THEN
  (match c.wp_ob with Some ob -> ADDR_LINEAR_BASES_TAC [ob] | None -> ALL_TAC) THEN
  MAP_EVERY (fun t ->
     FIRST_X_ASSUM(fun th ->
       if can (term_match [] (subst [t,`a:int64`] `read (memory :> bytes32 a) s = v`)) (concl th)
       then STRIP_ASSUME_TAC(CONV_RULE(READ_MEMORY_SPLIT_CONV 2) th) else NO_TAC))
   stores THEN
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read (memory :> bytes8 a) s = v`) (concl th)
     then CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THENC
                    REWRITE_CONV[GSYM ADD_ASSOC] THENC NUM_REDUCE_CONV) th else th) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  LOOP_TEST_TAC THEN PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`; GSYM ADD_ASSOC] THEN
      CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(REWRITE_TAC[maskth; READ_COMPONENT_COMPOSE; READ_ZEROTOP_128] THEN
      ASM_REWRITE_TAC[W1P_ZX_JOIN] THEN NO_TAC) THEN
  TRY(REWRITE_TAC[CHUNK_OUTPUT_SPLIT_N 8] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[ADD_CLAUSES; GSYM ADD_ASSOC] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[mld_polyw1_pack_32] THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      UNFOLD_ALL_ABBREVS_TAC THEN REPEAT CONJ_TAC THEN
      CONV_TAC(SIMD_SIMPLIFY_CONV []) THEN APP_BLAST_TAC `x:num->int32` THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let W1PACK4G_TAC exec c =
  W1P4_SETUP_TAC exec c THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC; W1P4_PRE_TAC exec; W1P4_BODY_TAC exec c THEN W1P4_FIN_TAC c; FULL_EXIT0_TAC];;

let PROVE_W1PACK4G c =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (c.wp_fn^"_"^c.wp_start), layout (c.wp_fn^"_"^c.wp_exit))] in
  prove(W1PACK4G_STMT c, W1PACK4G_TAC exec c);;


(* ------------------------------------------------------------------------- *)
(* The rolled row loop of ML-DSA-87 that decomposes w and packs w1 (loop 42 *)
(* of mldsa87_signature_internal): for each of the 8 rows k (RDX = k), the   *)
(* row at RCX = rsp0 + wo + 1024 k is decomposed in place with its high part *)
(* at rsp0 + ho (DECOMP32 through the pointer RCX), and the high part packed *)
(* to RAX - 4 = rsp0 + oo + 128 k (W1PACK4G through RAX). The statement is   *)
(* about the whole vector x of 8 rows at rsp0 + wo: the low parts replace it *)
(* and w1 = mld_sign_w1 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128 x *)
(* is at rsp0 + oo, the forms in which the caller needs them. The two inner  *)
(* loops are called as region lemmas.                                        *)
(* ------------------------------------------------------------------------- *)

type dr_cfg =
  {dr_fn: string; dr_start: string; dr_loop: string; dr_exit: string;
   dr_wo: int; dr_ho: int; dr_oo: int;
   dr_dec: thm; dr_pack: thm};;

let DW1R_MASK = "0x000000ff000000ff000000ff000000ff";;

let dr_sub c s =
  subst_tokens
   ["@FN@",c.dr_fn; "@MC@",image_mc; "@START@",c.dr_start; "@LOOP@",c.dr_loop;
    "@EXIT@",c.dr_exit; "@WO@",string_of_int c.dr_wo; "@HO@",string_of_int c.dr_ho;
    "@OO@",string_of_int c.dr_oo; "@OO4@",string_of_int (c.dr_oo + 4);
    "@MASK@",DW1R_MASK] s;;

let DW1R_STMT c = parse_term(dr_sub c
  "exists f_events.
  forall e rsp0 pc (x:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    aligned 16 (word_add rsp0 (word @HO@)) /\\
    PAIRWISE nonoverlapping
     [(word_add rsp0 (word @WO@),8192); (word_add rsp0 (word @HO@),1024);
      (word_add rsp0 (word @OO@),1024); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) @MC@ /\\
              read RIP s = word (pc + @FN@_@START@) /\\
              read RSP s = rsp0 /\\ read XMM6 s = word @MASK@ /\\
              (!i. i < 2048 ==> read (memory :> bytes32 (word_add rsp0 (word (@WO@ + 4 * i)))) s = x i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + @FN@_@EXIT@) /\\
              read RSP s = rsp0 /\\ read XMM6 s = word @MASK@ /\\
              (!i. i < 2048 ==> read (memory :> bytes32 (word_add rsp0 (word (@WO@ + 4 * i)))) s =
                                mld_polyvec_map mld_poly_decompose_lo_32 x i) /\\
              (!t. t < 1024 ==> read (memory :> bytes8 (word_add rsp0 (word (@OO@ + t)))) s =
                                mld_sign_w1 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128 x t) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 pc /\\
                 memaccess_inbounds e2
                  [word_add rsp0 (word @WO@),8192; word_add rsp0 (word @HO@),1024;
                   word_add rsp0 (word @OO@),1024]
                  [word_add rsp0 (word @WO@),8192; word_add rsp0 (word @HO@),1024;
                   word_add rsp0 (word @OO@),1024]))
         (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; RDI; R8; R9] ,,
          MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes(word_add rsp0 (word @WO@),8192);
                     memory :> bytes(word_add rsp0 (word @HO@),1024);
                     memory :> bytes(word_add rsp0 (word @OO@),1024)])");;

(*** a subregion of a region apart from another stays apart from it ***)

let DW1R_NONOV_SUB = prove
 (`!op:int64 n m pc sz len.
        n + m <= len /\ len < 2 EXP 64 /\ nonoverlapping (op,len) (pc,sz)
        ==> nonoverlapping (word_add op (word n),m) (pc,sz)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[nonoverlapping; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  MP_TAC(SPECL [`2 EXP 64`; `val(op:int64)`; `len:num`; `val(pc:int64)`; `sz:num`;
                `(val(op:int64) + n MOD 2 EXP 64) MOD 2 EXP 64`; `m:num`;
                `val(pc:int64)`; `sz:num`] NONOVERLAPPING_MODULO_SUBREGIONS) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[nonoverlapping; DIMINDEX_64] o
        check (fun th -> can (term_match [] `nonoverlapping (a,l) (b,m)`) (concl th))) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[CONTAINED_MODULO_LMOD] THEN
      SUBGOAL_THEN `n MOD 2 EXP 64 = n` SUBST1_TAC THENL
       [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC CONTAINED_MODULO_OFFSET_SIMPLE THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[CONTAINED_MODULO_REFL; LE_REFL]];
    SIMP_TAC[]]);;

(*** the coefficients of the vector forms ***)

let DW1R_LO = prove
 (`!x i. mld_polyvec_map mld_poly_decompose_lo_32 x i = mld_decompose_lo_32 (x i)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mld_polyvec_map; mld_polyvec; mld_poly_of; mld_poly_decompose_lo_32] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(SPECL [`i:num`; `256`] DIVISION) THEN ARITH_TAC);;

let DW1R_W1 = prove
 (`!x t. mld_sign_w1 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128 x t =
         mld_polyw1_pack_32 (mld_poly_decompose_hi_32 x) t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mld_sign_w1; mld_polyvec_pack; o_THM; mld_polyw1_pack_32;
              mld_poly_decompose_hi_32; mld_poly_of] THEN
  MP_TAC(SPECL [`t:num`; `128`] DIVISION) THEN CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_EQ_CONV)) THEN
  REWRITE_TAC[] THEN
  MAP_EVERY ABBREV_TAC [`q = t DIV 128`; `r = t MOD 128`] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `2 * (q * 128 + r) = 256 * q + 2 * r`;
              ARITH_RULE `2 * (q * 128 + r) + 1 = 256 * q + 2 * r + 1`]);;

let DW1R_W1_ROW = prove
 (`!x k j. mld_polyw1_pack_32 (mld_poly_decompose_hi_32 x) (128 * k + j) =
           mld_polyw1_pack_32 (mld_poly_decompose_hi_32 (mld_poly_of x k)) j`,
  REWRITE_TAC[mld_polyw1_pack_32; mld_poly_decompose_hi_32; mld_poly_of] THEN
  REWRITE_TAC[ARITH_RULE `2 * (128 * k + j) = 256 * k + 2 * j`;
              ARITH_RULE `2 * (128 * k + j) + 1 = 256 * k + 2 * j + 1`; ADD_ASSOC]);;

let DW1R_TEST = prove
 (`!k. k < 8
       ==> (val(word_add (word k) (word 18446744073709551609):int64) = 0 <=> ~(k + 1 < 8))`,
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC NUM_REDUCE_CONV);;

(*** row k of the vector in memory: taken out of the rest, and put back ***)

let DW1R_SLICE = prove
 (`!(B:int64) wo k (x:num->int32) (s:x86state).
     (!i. 256 * k <= i /\ i < 2048
          ==> read (memory :> bytes32 (word_add B (word (wo + 4 * i)))) s = x i) /\
     k < 8
     ==> (!i. i < 256
              ==> read (memory :> bytes32 (word_add B (word ((wo + 1024 * k) + 4 * i)))) s =
                  mld_poly_of x k i) /\
         (!i. 256 * (k + 1) <= i /\ i < 2048
              ==> read (memory :> bytes32 (word_add B (word (wo + 4 * i)))) s = x i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[ARITH_RULE `(wo + 1024 * k) + 4 * i = wo + 4 * (256 * k + i)`; mld_poly_of] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`i < 256`; `k < 8`] THEN ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`256 * (k + 1) <= i`; `i < 2048`] THEN ARITH_TAC]);;

let DW1R_JOIN32 = prove
 (`!(B:int64) wo k (f:num->int32) (s:x86state).
     (!i. i < 256 * k
          ==> read (memory :> bytes32 (word_add B (word (wo + 4 * i)))) s = f i) /\
     (!i. i < 256
          ==> read (memory :> bytes32 (word_add B (word ((wo + 1024 * k) + 4 * i)))) s =
              f (256 * k + i))
     ==> !i. i < 256 * (k + 1)
             ==> read (memory :> bytes32 (word_add B (word (wo + 4 * i)))) s = f i`,
  REWRITE_TAC[ARITH_RULE `(wo + 1024 * k) + 4 * i = wo + 4 * (256 * k + i)`] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `i < 256 * k` THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i - 256 * k`) THEN
  ANTS_TAC THENL [MAP_EVERY UNDISCH_TAC [`i < 256 * (k + 1)`; `~(i < 256 * k)`] THEN ARITH_TAC;
                  ALL_TAC] THEN
  SUBGOAL_THEN `256 * k + (i - 256 * k) = i` (fun th -> REWRITE_TAC[th]) THEN
  UNDISCH_TAC `~(i < 256 * k)` THEN ARITH_TAC);;

let DW1R_JOIN8 = prove
 (`!(B:int64) oo k (f:num->byte) (s:x86state).
     (!t. t < 128 * k
          ==> read (memory :> bytes8 (word_add B (word (oo + t)))) s = f t) /\
     (!j. j < 128
          ==> read (memory :> bytes8 (word_add B (word ((oo + 128 * k) + j)))) s =
              f (128 * k + j))
     ==> !t. t < 128 * (k + 1)
             ==> read (memory :> bytes8 (word_add B (word (oo + t)))) s = f t`,
  REWRITE_TAC[ARITH_RULE `(oo + 128 * k) + j = oo + (128 * k + j)`] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `t < 128 * k` THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t - 128 * k`) THEN
  ANTS_TAC THENL [MAP_EVERY UNDISCH_TAC [`t < 128 * (k + 1)`; `~(t < 128 * k)`] THEN ARITH_TAC;
                  ALL_TAC] THEN
  SUBGOAL_THEN `128 * k + (t - 128 * k) = t` (fun th -> REWRITE_TAC[th]) THEN
  UNDISCH_TAC `~(t < 128 * k)` THEN ARITH_TAC);;

let DW1R_INV c = parse_term(dr_sub c
  "\\k s. read RSP s = rsp0 /\\ read RDX s = word k /\\
         read RCX s = word_add rsp0 (word (@WO@ + 1024 * k)) /\\
         read RAX s = word_add rsp0 (word (@OO4@ + 128 * k)) /\\
         read XMM6 s = word @MASK@ /\\
         (!j. 256 * k <= j /\\ j < 2048
              ==> read (memory :> bytes32 (word_add rsp0 (word (@WO@ + 4 * j)))) s = x j) /\\
         (!j. j < 256 * k
              ==> read (memory :> bytes32 (word_add rsp0 (word (@WO@ + 4 * j)))) s =
                  mld_decompose_lo_32 (x j)) /\\
         (!t. t < 128 * k
              ==> read (memory :> bytes8 (word_add rsp0 (word (@OO@ + t)))) s =
                  mld_polyw1_pack_32 (mld_poly_decompose_hi_32 x) t)");;

let DW1R_ALLOWED = [`rsp0:int64`; `pc:num`; `x:num->int32`; `k:num`];;

let DW1R_PRE_TAC =
  REPEAT CONJ_TAC THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
  VM_PRE_TAC DW1R_ALLOWED;;

let DW1R_CALL_TAC execth name ilist n =
  REMOVE_THEN name (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,execth,0x0,
       mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,th)
      (`e:(uarch_event)list`::ilist) n THENL
     [DW1R_PRE_TAC; LABEL_TAC name th]);;

(* the nonoverlapping of the regions of row k (its coefficients at rsp0 + wo
   + 1024 k, its packed bytes at rsp0 + oo + 128 k), and row k taken out of
   the coefficients not yet decomposed *)
let DW1R_ROW_FACTS_TAC c =
  let wo = c.dr_wo and oo = c.dr_oo in
  let tm s = parse_term(dr_sub c s) in
  SUBGOAL_THEN (tm
   "nonoverlapping (word_add (rsp0:int64) (word (@WO@ + 1024 * k)),1024) (word_add rsp0 (word @HO@),1024) /\\
    nonoverlapping (word_add rsp0 (word (@WO@ + 1024 * k)),1024) (word pc,libmldsa_size) /\\
    nonoverlapping (word_add rsp0 (word (@OO@ + 128 * k)),128) (word_add rsp0 (word @HO@),1024) /\\
    nonoverlapping (word_add rsp0 (word (@OO@ + 128 * k)),128) (word pc,libmldsa_size)")
   STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[WORD_RULE (subst [mk_small_numeral wo,`wo:num`]
                 `word_add (rsp0:int64) (word (wo + 1024 * k)) = word_add (word_add rsp0 (word wo)) (word (1024 * k))`);
                WORD_RULE (subst [mk_small_numeral oo,`oo:num`]
                 `word_add (rsp0:int64) (word (oo + 128 * k)) = word_add (word_add rsp0 (word oo)) (word (128 * k))`)] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC DW1R_NONOV_SUB THEN
    FIRST (map (fun l ->
      EXISTS_TAC l THEN
      REPEAT CONJ_TAC THENL
       [ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV;
        FIRST_ASSUM(fun th -> ACCEPT_TAC th ORELSE
                              ACCEPT_TAC(ONCE_REWRITE_RULE[NONOVERLAPPING_SYM] th))])
      [`8192`; `1024`]);
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && free_in `x:num->int32` (concl th) &&
       not(free_in `mld_decompose_lo_32` (concl th)) &&
       not(free_in `mld_poly_decompose_hi_32` (concl th))
    then MP_TAC(MATCH_MP DW1R_SLICE (CONJ th (ASSUME `k < 8`))) else NO_TAC) THEN
  STRIP_TAC;;

let DW1R_BODY1_TAC execth c =
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  FULL_INIT_TAC THEN X86_STEPS_TAC execth (1--2) THEN
  DW1R_ROW_FACTS_TAC c;;

let DW1R_BODY2_TAC execth c =
  let wo = c.dr_wo and oo = c.dr_oo in
  let num = mk_small_numeral in
  let rowa = subst [num wo,`wo:num`] `word_add rsp0 (word (wo + 1024 * k)):int64`
  and opa = subst [num oo,`oo:num`] `word_add rsp0 (word (oo + 128 * k)):int64` in
  let xk = `mld_poly_of (x:num->int32) k` in
  DW1R_CALL_TAC execth "H_DEC" [rowa; `rsp0:int64`; `pc:num`; xk] 3 THEN
  DW1R_CALL_TAC execth "H_PACK"
    [`rsp0:int64`; opa; `pc:num`; mk_comb(`mld_poly_decompose_hi_32`,xk)] 4 THEN
  X86_STEPS_TAC execth (5--9);;

let DW1R_SUB128 = WORD_BLAST
 `word_sub (x:int64) (word 18446744073709551488) = word_add x (word 128)`;;

(* the invariant for k + 1: the row k put back into the decomposed
   coefficients and the packed bytes, the registers and the loop test *)
let DW1R_FIN_TAC c =
  let wo = mk_small_numeral c.dr_wo and oo = mk_small_numeral c.dr_oo in
  let j32 = BETA_RULE(ISPECL [`rsp0:int64`; wo; `k:num`; `\j. mld_decompose_lo_32 ((x:num->int32) j)`]
                       DW1R_JOIN32)
  and j8 = ISPECL [`rsp0:int64`; oo; `k:num`; `mld_polyw1_pack_32 (mld_poly_decompose_hi_32 (x:num->int32))`]
             DW1R_JOIN8 in
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `k:num` DW1R_TEST) (ASSUME `k < 8`)]) THEN
  RULE_ASSUM_TAC(fun th ->
    if is_forall(concl th) && free_in `mld_poly_of:(num->int32)->num->num->int32` (concl th)
    then REWRITE_RULE[mld_poly_decompose_lo_32; mld_poly_of]
           (REWRITE_RULE[GSYM DW1R_W1_ROW] th)
    else th) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(REWRITE_TAC[ARITH_RULE `1024 * (k + 1) = 1024 * k + 1024`;
                  ARITH_RULE `128 * (k + 1) = 128 * k + 128`; DW1R_SUB128] THEN
      CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC j32 THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC j8 THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
  SIGN_LOOP_DISCHARGE_TAC;;

let DW1R_BODY_TAC execth c =
  DW1R_BODY1_TAC execth c THEN DW1R_BODY2_TAC execth c THEN DW1R_FIN_TAC c;;

let DW1R_SETUP_TAC execth c =
  ASSUME_CALLEE_SAFETY_TAILED_TAC c.dr_dec "H_DEC" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC c.dr_pack "H_PACK" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (pc:num).
      APPEND (f_ev_epil rsp0 pc)
       (APPEND (ENUMERATEL 8 (\k. f_ev_row rsp0 pc k)) (f_ev_prol rsp0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `pc:num`; `x:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; ALL; PAIRWISE; fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[DW1R_LO; DW1R_W1] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `8` (parse_term(dr_sub c "pc + @FN@_@LOOP@"))
   (parse_term(dr_sub c "pc + @FN@_@EXIT@")) (DW1R_INV c);;

let DW1R_TAC c =
  let execth = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (c.dr_fn^"_"^c.dr_start), layout (c.dr_fn^"_"^c.dr_exit))] in
  DW1R_SETUP_TAC execth c THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    (* to the head of the loop *)
    FULL_INIT_TAC THEN X86_STEPS_TAC execth (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    (* row k *)
    DW1R_BODY_TAC execth c;
    (* the exit *)
    FULL_EXIT0_TAC];;

let PROVE_DW1R c = prove(DW1R_STMT c, DW1R_TAC c);;

(* ------------------------------------------------------------------------- *)
(* mld_polyw1_unpack_32 (gamma2 = (q - 1) / 32) of the 128 bytes b at rsp0 + *)
(* ib as clang vectorises it in the hints of ML-DSA-65/87: 32 iterations,   *)
(* each reading 4 bytes ([rsp + idx + ib] by MOVD and [.. + 2] by MOVZWL    *)
(* into tmp), splitting the nibbles with PSRLW, PUNPCKLBW and the mask in   *)
(* XMM5, widening with PUNPCKLBW/PUNPCKLWD against zero (XMM4), and storing *)
(* 8 coefficients at [rsp + idx * 8 + ob] and + 16, idx = 4 i. The mask is   *)
(* the image constant mldsaNN_signature_internal_const3 that the code loads  *)
(* into XMM5 (bytes 0f 0f 0f 0f 00 0f 00 0f ..; only its low 4 bytes are     *)
(* used).                                                                    *)
(* ------------------------------------------------------------------------- *)

let W1U4_MASK = "0x0f000f000f000f000f000f000f0f0f0f";;

let W1UNPACK4_STMT fn loop exit idx tmp ib ob =
  parse_term(subst_tokens
   ["@FN@",fn; "@MC@",image_mc; "@LOOP@",loop; "@EXIT@",exit; "@IDX@",idx; "@TMP@",tmp;
    "@IB@",string_of_int ib; "@OB@",string_of_int ob; "@MASK@",W1U4_MASK]
  "exists f_events.
  forall e rsp0 pc (b:num->byte).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    aligned 16 (word_add rsp0 (word @OB@)) /\\
    ALL (nonoverlapping (word_add rsp0 (word @OB@),1024))
        [(word_add rsp0 (word @IB@),128); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) @MC@ /\\
              read RIP s = word (pc + @FN@_@LOOP@) /\\
              read RSP s = rsp0 /\\ read @IDX@ s = word 0 /\\
              read XMM4 s = word 0 /\\ read XMM5 s = word @MASK@ /\\
              (!j. j < 128 ==> read(memory :> bytes8(word_add rsp0 (word (@IB@ + j)))) s = b j) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + @FN@_@EXIT@) /\\
              read RSP s = rsp0 /\\ read @IDX@ s = word 128 /\\
              read XMM4 s = word 0 /\\ read XMM5 s = word @MASK@ /\\
              (!j. j < 128 ==> read(memory :> bytes8(word_add rsp0 (word (@IB@ + j)))) s = b j) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (@OB@ + 4*i)))) s =
                               mld_polyw1_unpack_32 b i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 pc /\\
                 memaccess_inbounds e2 [word_add rsp0 (word @IB@),128; word_add rsp0 (word @OB@),1024]
                                       [word_add rsp0 (word @OB@),1024]))
         (MAYCHANGE [RIP; @IDX@; @TMP@] ,, MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes(word_add rsp0 (word @OB@),1024)])");;

let W1U4_LANES =
  let mk k =
    let e = if k = 0 then "8 * i" else Printf.sprintf "8 * i + %d" k
    and bi = if k / 2 = 0 then "4 * i" else Printf.sprintf "4 * i + %d" (k / 2) in
    let rhs =
      if k mod 2 = 0 then Printf.sprintf "word_and (word_zx ((b:num->byte) (%s)):int32) (word 15)" bi
      else Printf.sprintf "word_ushr (word_zx ((b:num->byte) (%s)):int32) 4" bi in
    prove(parse_term(Printf.sprintf "!b:num->byte. !i. mld_polyw1_unpack_32 b (%s) = %s" e rhs),
          REPEAT GEN_TAC THEN REWRITE_TAC[mld_polyw1_unpack_32] THEN
          CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
          REWRITE_TAC[ARITH_RULE(parse_term(Printf.sprintf "%s = 2 * (%s) + %d" e bi (k mod 2)))] THEN
          REWRITE_TAC[MP (SPECL [`2`; parse_term bi; mk_small_numeral (k mod 2)] DIVMOD_CHUNK)
                         (ARITH_RULE(parse_term(Printf.sprintf "%d < 2" (k mod 2))))] THEN
          CONV_TAC NUM_REDUCE_CONV) in
  map mk (0--7);;

let W1U4_FIN_TAC ob =
  let wide = map (fun k -> parse_term(Printf.sprintf
    "word_add rsp0 (word (8 * (4 * i) + %d)):int64" (ob + k))) [0; 16] in
  MAP_EVERY (fun t ->
     FIRST_X_ASSUM(fun th ->
       if can (term_match [] (subst [t,`a:int64`] `read (memory :> bytes128 a) s = v`)) (concl th)
       then STRIP_ASSUME_TAC(CONV_RULE(READ_MEMORY_SPLIT_CONV 2) th) else NO_TAC)) wide THEN
  CHUNKN_FULL_FINAL_TAC [ob] 8
    [ARITH_RULE `4 * (i + 1) = 4 * i + 4`; ARITH_RULE `8 * (i + 1) = 8 * i + 8`]
    (REWRITE_TAC[XMM4; XMM5; READ_COMPONENT_COMPOSE; READ_ZEROTOP_128] THEN
     ASM_REWRITE_TAC[W1P_ZX_JOIN])
    (REWRITE_TAC W1U4_LANES THEN UNFOLD_ALL_ABBREVS_TAC THEN REPEAT CONJ_TAC THEN
     CONV_TAC(SIMD_SIMPLIFY_CONV []) THEN APP_BLAST_TAC `b:num->byte`);;

(* the bytes 4 i + k of b (k < 4) at the addresses ib + (4 i + k) that
   MERGE_LIN_TAC_B gives the parts of the wide reads *)
let W1U4_BYTES_TAC ib =
  MAP_EVERY (fun k ->
    let bk = if k = 0 then "4 * i" else Printf.sprintf "4 * i + %d" k in
    let t = parse_term(Printf.sprintf
      "read (memory :> bytes8 (word_add rsp0 (word (%d + %s)))) s0 = (b:num->byte) (%s)" ib bk bk) in
    SUBGOAL_THEN t ASSUME_TAC THENL
     [FIRST_X_ASSUM(fun th ->
        if is_forall(concl th) && free_in `b:num->byte` (concl th) then
          MATCH_MP_TAC th THEN ASSUME_TAC th else NO_TAC) THEN
      ASM_ARITH_TAC;
      ALL_TAC]) (0--3);;

let W1U4_SETUP_TAC exec fn loop exit idx ib ob =
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (pc:num).
      APPEND (f_ev_epil rsp0 pc)
       (APPEND (ENUMERATEL 32 (\i. f_ev_loop rsp0 pc i)) (f_ev_prol rsp0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `pc:num`; `b:num->byte`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(subst_tokens ["@IDX@",idx; "@IB@",string_of_int ib; "@OB@",string_of_int ob;
                             "@MASK@",W1U4_MASK]
   "\\i s. read RSP s = rsp0 /\\ read @IDX@ s = word (4 * i) /\\
          read XMM4 s = word 0 /\\ read XMM5 s = word @MASK@ /\\
          (!j. j < 128 ==> read(memory :> bytes8(word_add rsp0 (word (@IB@ + j)))) s = b j) /\\
          (!j. j < 8 * i
               ==> read(memory :> bytes32(word_add rsp0 (word(@OB@ + 4 * j)))) s =
                   mld_polyw1_unpack_32 b j)")) THEN
  ALL_TAC;;

let W1U4_PRE_TAC =
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;;

let W1U4_BODY_TAC exec ib ob =
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MAP_EVERY (fun n -> GHOST_INTRO_TAC (mk_var(Printf.sprintf "ymm%d_init" n,`:int256`))
                         (parse_term(Printf.sprintf "read YMM%d" n))) [0;1;2;3] THEN
    FULL_INIT_TAC THEN
    XMM_EXISTSTOP_TAC "top4" `YMM4` THEN XMM_EXISTSTOP_TAC "top5" `YMM5` THEN
    VAL_INT64_TAC `4 * i` THEN
    W1U4_BYTES_TAC ib THEN
    MERGE_LIN_TAC_B 2 [ib] (parse_term(Printf.sprintf
      "read (memory :> bytes32 (word_add rsp0 (word (1 * (4 * i) + %d)))) s0" ib)) THEN
    MERGE_LIN_TAC_B 1 [ib] (parse_term(Printf.sprintf
      "read (memory :> bytes16 (word_add rsp0 (word (1 * (4 * i) + %d)))) s0" (ib + 2))) THEN
    MAP_EVERY (fun k -> ALIGN16_IDX_TAC `rsp0:int64`
      (parse_term(Printf.sprintf "8 * (4 * i) + %d" (ob + k)))) [0; 16] THEN
    (fun g -> abbrev_ctr () := 0; ALL_TAC g) THEN
    ABBREV_YMM_STEPS_TAC exec (1--17) THEN X86_STEPS_TAC exec (18--20);;

let W1UNPACK4_TAC exec fn loop exit idx ib ob =
  W1U4_SETUP_TAC exec fn loop exit idx ib ob THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC; W1U4_PRE_TAC; W1U4_BODY_TAC exec ib ob THEN W1U4_FIN_TAC ob; FULL_EXIT0_TAC];;

let PROVE_W1UNPACK4 fn loop exit idx tmp ib ob =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(W1UNPACK4_STMT fn loop exit idx tmp ib ob, W1UNPACK4_TAC exec fn loop exit idx ib ob);;

(* ------------------------------------------------------------------------- *)
(* c~ = H(mu || w1) in mldsa87_signature_internal, which clang inlines as in *)
(* mldsa87_verify_internal (C2 of inline_verify87.ml): the 64 bytes of mu at *)
(* rsp0 + mo and the 1024 bytes of w1 at rsp0 + wo are absorbed into the     *)
(* Keccak state at rsp0 + so as 8 full blocks of 136 bytes (the first from   *)
(* mu and the first 72 bytes of w1, the 7 others by the loop over the blocks *)
(* with the pointer into w1 in R15, stepped through as straight-line code),  *)
(* then the padding and the last permutation. The code is that of verify's  *)
(* C2 with other offsets and registers: the state is zeroed from XMM5 (zero  *)
(* at the start), its address is in R14 before the region (RDI of the        *)
(* permutations of the blocks), the position at rsp0 + so + 200 is written,  *)
(* and RBX = rsp0 + so at the end. The code also loads the multiplier        *)
(* constant of the loop over z into R14 before the padding, which the post   *)
(* states for the stage that follows. The frame is stated from fb = rsp0 -   *)
(* 296 (the stack of the permutation) to the end of the state.               *)
(* ------------------------------------------------------------------------- *)

type c2s_cfg =
  {c2_fn: string; c2_start: string; c2_end: string;
   c2_so: int; c2_mo: int; c2_wo: int};;

let c2s_sub c s =
  subst_tokens
   ["@FN@",c.c2_fn; "@MC@",image_mc; "@START@",c.c2_start; "@END@",c.c2_end;
    "@SO@",string_of_int c.c2_so; "@MO@",string_of_int c.c2_mo; "@WO@",string_of_int c.c2_wo;
    "@FL@",string_of_int (296 + c.c2_so + 208)] s;;

let C2S_STMT c = parse_term(c2s_sub c
  "exists f_events.
   forall e rsp0 pc MU W1.
     aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
     aligned 32 (rsp0:int64) /\\
     nonoverlapping (word_sub rsp0 (word 296),@FL@) (word pc,libmldsa_size)
     ==> ensures x86
          (\\s. bytes_loaded s (word pc) @MC@ /\\
               read RIP s = word (pc + @FN@_@START@) /\\
               read RSP s = rsp0 /\\ read R14 s = word_add rsp0 (word @SO@) /\\
               read XMM5 s = word 0 /\\
               read (memory :> bytes(word_add rsp0 (word @MO@),64)) s = MU /\\
               read (memory :> bytes(word_add rsp0 (word @WO@),1024)) s = W1 /\\
               read events s = e)
          (\\s. read RIP s = word (pc + @FN@_@END@) /\\
               read RSP s = rsp0 /\\ read RBX s = word_add rsp0 (word @SO@) /\\
               read R14 s = word 0x0380200100000000 /\\
               read (memory :> wbytes (word_add rsp0 (word @SO@))) s =
               keccak_f1600 (mld_shake256_state 1088 (MU + 2 EXP 512 * W1)) /\\
               (exists e2. read events s = APPEND e2 e /\\
                  e2 = f_events (word_sub rsp0 (word 296)) pc /\\
                  memaccess_inbounds e2
                   [word_add rsp0 (word @MO@),64; word_add rsp0 (word @WO@),1024;
                    word_sub rsp0 (word 296),@FL@;
                    word(pc + rodata_mld_KeccakF_RoundConstants),192]
                   [word_sub rsp0 (word 296),@FL@]))
          (MAYCHANGE [RSP; RBX; R12; R13; R14; R15] ,,
           MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub rsp0 (word 296),296);
                      memory :> bytes(word_add rsp0 (word @SO@),208)])");;

(*** One block k = 1..7 of the loop (as C2_BLOCK_TAC), the state at a and ***)
(*** w1 at w1                                                             ***)

let C2S_BLOCK_TAC execth (a:term) (w1:term) k n0 =
  let ncall = n0 + 33 in
  let sn = mk_var("s"^string_of_int(n0 + 32),`:x86state`) in
  let sv = mk_var("st"^string_of_int k,`:1600 word`)
  and wv = mk_var("wb"^string_of_int k,`:1600 word`) in
  let off j = 72 + 136 * (k - 1) + 16 * j in
  TR_STATE_CHUNKS_TAC a (0--7) (16--24) THEN
  MAP_EVERY (fun j -> C2_SRC_TAC k 128 (128 * j) w1 1024 (off j)) (0--7) THEN
  C2_SRC_TAC k 64 1024 w1 1024 (off 8) THEN
  TR_NAME_TAC (tr_st k) ("st"^string_of_int k) THEN
  TR_NAME_TAC (tr_wb k) ("wb"^string_of_int k) THEN
  X86_STEPS_TAC execth ((n0+1)--(n0+32)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO; VERIF_SUBWORD_JOIN_HI]) THEN
  C2_REG_NORM_TAC THEN
  MP_TAC(SPECL [a; sv; wv; sn] TR_BLK_MERGE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL
     [ALL_TAC; TR_UNNAME_GOAL_TAC ("wb"^string_of_int k)]]] THEN
    TRG_ANTE_TAC 1088;
    DISCH_TAC] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc execth "H_PERM"
   [`read RDI s`; mk_comb(mk_comb(`word_xor:1600 word->1600 word->1600 word`,sv),wv);
    `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   [`fb:int64`; `pc:num`] ncall THEN
  TR_UNNAME_TAC ("st"^string_of_int k) THEN
  TR_UNNAME_TAC ("wb"^string_of_int k) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TR_BLOCKS_STEP k]) THEN
  YMM_GHOST_TAC (mk_var("s"^string_of_int ncall,`:x86state`))
   ["YMM0","y0_"^string_of_int k; "YMM1","y1_"^string_of_int k] THEN
  X86_STEPS_TAC execth ((ncall+1)--(ncall+3)) THEN C2_RIP_TAC;;

(* The steps of the code of signing (the counts differ from verify's): 11
   zeroing stores (the first a MOVDQU at so + 188), block 0 to the CALL at
   step 36, 4 instructions to the loop, the 7 blocks of 36 steps, 3
   instructions to the padding (TEST, MOVABS to R14, JE) and 7 to the CALL
   of the last permutation. *)
let C2S_TAC c =
  let execth = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (c.c2_fn^"_"^c.c2_start), layout (c.c2_fn^"_"^c.c2_end))] in
  let ao = 296 + c.c2_so in
  let a = tr_fb_add ao in
  let mu = tr_fb_add (296 + c.c2_mo) and w1 = tr_fb_add (296 + c.c2_wo) in
  let x5tm = `word_subword (ymm5_init:int256) (0,128):int128 = word 0` in
  let X5RW_TAC = RULE_ASSUM_TAC(fun th -> if concl th = x5tm then th
                                         else REWRITE_RULE[ASSUME x5tm] th) in
  let bound_tac src len =
    FIRST_ASSUM(fun th ->
      if can (term_match [] (subst [src,`a:int64`; mk_small_numeral len,`n:num`]
                `read (memory :> bytes(a,n)) (s:x86state) = x`)) (concl th)
      then let st = rand(lhs(concl th)) in
           let b = ISPECL [src; mk_small_numeral len;
                           mk_comb(`read memory:x86state->int64->byte`,st)] READ_BYTES_BOUND in
           ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
                       (REWRITE_RULE[GSYM READ_COMPONENT_COMPOSE; th] b))
      else NO_TAC) in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERM" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(fb:int64) (pc:num). f_ev_all fb pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  X_GEN_TAC `e:(uarch_event)list` THEN WORD_FORALL_OFFSET_TAC 296 THEN
  MAP_EVERY X_GEN_TAC [`fb:int64`; `pc:num`; `MU:num`; `W1:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  TR_ALIGNED_TAC 296 ((map (fun j -> c.c2_so + 16 * j) (0--11)) @
                      (map (fun j -> c.c2_mo + 16 * j) (0--3)) @
                      (map (fun j -> c.c2_wo + 16 * j) (0--3))) THEN
  ABBREV_TAC `PK = MU + 2 EXP 512 * W1` THEN
  GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
  GHOST_INTRO_TAC `ymm2_init:int256` `read YMM2` THEN
  GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN
  GHOST_INTRO_TAC `ymm5_init:int256` `read YMM5` THEN
  FULL_INIT_TAC THEN
  SUBGOAL_THEN x5tm ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (term_match [] `read XMM5 s = x:int128`) (concl th))) THEN
    ASM_REWRITE_TAC[XMM5; READ_COMPONENT_COMPOSE; READ_ZEROTOP_128] THEN
    CONV_TAC WORD_BLAST;
    ALL_TAC] THEN
  C2_REG_NORM_TAC THEN
  bound_tac mu 64 THEN bound_tac w1 1024 THEN
  SUBGOAL_THEN `PK < 2 EXP 8704` ASSUME_TAC THENL
   [EXPAND_TAC "PK" THEN
    MATCH_MP_TAC(ARITH_RULE `a < 2 EXP 512 /\ b < 2 EXP 8192
                             ==> a + 2 EXP 512 * b < 2 EXP 8704`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the zeroing of the state from byte 32 *)
  X86_STEPS_TAC execth (1--1) THEN X5RW_TAC THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] (subst [mk_small_numeral (ao + 188),`n:num`]
              `read (memory :> bytes128 (word_add fb (word n))) s1 = x`)) (concl th)
    then STRIP_ASSUME_TAC(CONV_RULE(READ_MEMORY_SPLIT_CONV 2) th) else NO_TAC) THEN
  ADDR_NORMALIZE_TAC THEN
  X86_STEPS_TAC execth (2--11) THEN X5RW_TAC THEN
  MAP_EVERY (fun j ->
    FIRST_X_ASSUM(fun th ->
      if can (term_match [] (subst [mk_small_numeral (ao + 16 * j),`n:num`]
               `read (memory :> bytes128 (word_add fb (word n))) s11 = x`)) (concl th)
      then STRIP_ASSUME_TAC(CONV_RULE(READ_MEMORY_SPLIT_CONV 1) th) else NO_TAC)) (8--11) THEN
  ADDR_NORMALIZE_TAC THEN
  MP_TAC(CONV_RULE(RAND_CONV(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV))
     (READ_MEMORY_MERGE_CONV 1 (subst [mk_small_numeral (ao + 192),`n:num`]
        `read (memory :> bytes64 (word_add fb (word n))) s11`))) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN DISCH_TAC THEN
  (* block 0: mu and the first 72 bytes of w1 *)
  MAP_EVERY (fun j -> C2_SRC_TAC 0 128 (128 * j) mu 64 (16 * j)) (0--3) THEN
  MAP_EVERY (fun j -> C2_SRC_TAC 0 128 (512 + 128 * j) w1 1024 (16 * j)) (0--3) THEN
  C2_SRC_TAC 0 64 1024 w1 1024 64 THEN
  TR_NAME_TAC (tr_wb 0) "wb0" THEN
  X86_STEPS_TAC execth (12--36) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO; VERIF_SUBWORD_JOIN_HI]) THEN
  C2_REG_NORM_TAC THEN
  MP_TAC(SPECL [a; `word 0:1600 word`; `wb0:1600 word`; `s36:x86state`] TR_BLK_MERGE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL
     [ALL_TAC; TR_UNNAME_GOAL_TAC "wb0"]]] THEN
    TRG_ANTE_TAC 1088;
    DISCH_TAC] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc execth "H_PERM"
   [`read RDI s`; `word_xor (word 0) wb0:1600 word`;
    `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   [`fb:int64`; `pc:num`] 37 THEN
  TR_UNNAME_TAC "wb0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TR_BLOCKS_STEP 0]) THEN
  YMM_GHOST_TAC `s37:x86state` ["YMM0","y0_0"; "YMM1","y1_0"] THEN
  X86_STEPS_TAC execth (38--41) THEN
  C2_REG_NORM_TAC THEN
  (* the loop, 7 blocks *)
  MAP_EVERY (fun k -> C2S_BLOCK_TAC execth a w1 k (41 + 36 * (k - 1))) (1--7) THEN
  (* the test of the rest, the padding and the last permutation *)
  X86_STEPS_TAC execth (294--296) THEN C2_RIP_TAC THEN
  TR_STATE_CHUNKS_TAC a [] ((1--15) @ (17--24)) THEN
  TR_STATE_BYTES_TAC a ((0--7) @ (128--135)) THEN
  TR_NAME_TAC (tr_st 8) "st8" THEN
  X86_STEPS_TAC execth (297--303) THEN
  MP_TAC(SPECL [a; `st8:1600 word`; `s303:x86state`] TR_PAD0_MERGE) THEN
  ANTS_TAC THENL [TRG_ANTE_TAC 1088; DISCH_TAC] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc execth "H_PERM"
   [`read RDI s`;
    `word_xor (word_xor st8 (word(2 EXP 0 * 31))) (word(2 EXP 1080 * 128)):1600 word`;
    `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   [`fb:int64`; `pc:num`] 304 THEN
  TR_UNNAME_TAC "st8" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM(MATCH_MP C2_STATE_EQ (ASSUME `PK < 2 EXP 8704`))]) THEN
  C2_REG_NORM_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let PROVE_C2S c = prove(C2S_STMT c, C2S_TAC c);;
