(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* More regions that clang 23 -O3 inlines into mldsa-native's verify and     *)
(* signing functions in the monolithic reduced-RAM build, as lemmas from the *)
(* head of the code to its exit in the form of inline_sign.ml: the packing   *)
(* of w1, the constant-time comparison of c~ with c2, and the zeroing of the *)
(* buffers and the return at the end of verify_internal.                     *)
(*                                                                           *)
(* Three techniques keep the simulation of this code manageable:             *)
(*                                                                           *)
(*  - Aliases. The simulator rewrites the addresses of loads and stores with *)
(*    the equations among the assumptions. Where it forms an address that it *)
(*    cannot normalize, as base + (x + 2^64 - 2) for a displacement of -2,   *)
(*    an equation of that form with base + (x - 2) (ALIAS_ASSUME_TAC) makes  *)
(*    the access match the facts about memory, and keeps the other facts,    *)
(*    whose disjointness from a store it can then prove.                     *)
(*                                                                           *)
(*  - Abbreviations. In long SSE code without loops or branches, each new    *)
(*    register value is replaced by a fresh variable abN, with the inert     *)
(*    fact abbrev_def abN t (ABBREV_STEPS_TAC), so that the terms do not     *)
(*    grow with the steps; the result is then proved from the definitions    *)
(*    that it needs (UNFOLD_ABBREVS_TAC), by bit-blasting.                   *)
(*                                                                           *)
(*  - Calls of libc. After a call through a contract RSP is                  *)
(*    word_add (word_sub rsp (word 8)) (word 8); RSP_NORM_TAC puts it back   *)
(*    as rsp, as the addresses of the frame and the facts that they are      *)
(*    aligned are relative to rsp (an aligned SSE store whose alignment is   *)
(*    unknown does not return).                                              *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_verify.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sponge_b.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/keccakf1600_permute_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* Aliases: word_add p (word a) = word_add p (word b) for a = b + 2^64, and  *)
(* the equations of a list assumed, each proved so.                          *)
(* ------------------------------------------------------------------------- *)

let ALIAS64_TAC =
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN AP_TERM_TAC THEN
  W(fun (asl,w) ->
    let a = rand(lhs w) and b = rand(rhs w) in
    if a = b then REFL_TAC else
    let eq = (try ARITH_RULE(mk_eq(a,mk_binop `(+):num->num->num` b `18446744073709551616`))
              with Failure _ -> ARITH_RULE(mk_eq(a,b))) in
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [eq] THEN
    REWRITE_TAC[WORD_ADD; WORD_REDUCE_CONV `word 18446744073709551616:int64`; WORD_ADD_0]);;

let ALIAS_ASSUME_TAC (ss:string list) =
  MAP_EVERY (fun s -> SUBGOAL_THEN (parse_term s) ASSUME_TAC THENL [ALIAS64_TAC; ALL_TAC]) ss;;

(* ------------------------------------------------------------------------- *)
(* mld_polyw1_pack_88 of the polynomial x at c to the 192 bytes at op: 64     *)
(* iterations, each turning 4 coefficients (at RAX - 12, ..., RAX) into 3    *)
(* bytes, stored at [R13 + R8 - 2], [R13 + R8 - 1] and [R13 + R8]. R13 is    *)
(* op + 2 and R8 is 3 i. The simulator forms these addresses as sums with    *)
(* the displacement 2^64 - 2 (or 2^64 - 1) that it does not reduce, and the  *)
(* loads [RAX - 12] ... [RAX - 4] likewise, so the body first assumes the    *)
(* aliases of these forms with op + (3 i + k) and c + (16 i + k).            *)
(* ------------------------------------------------------------------------- *)

let PACKW1_ALIASES =
  let r k = if k = 0 then "3 * i" else Printf.sprintf "3 * i + %d" k in
  flat (map (fun (d,k) ->
    [Printf.sprintf "word_add (word_add op (word 2)) (word (1 * (3 * i) + %s)):int64 = word_add op (word (%s))" d (r k);
     Printf.sprintf "word_add (word_add (word_add op (word 2)) (word (1 * (3 * i)))) (word %s):int64 = word_add op (word (%s))" d (r k)])
   ["18446744073709551614",0; "18446744073709551615",1]) @
  ["word_add (word_add op (word 2)) (word (1 * (3 * i))):int64 = word_add op (word (3 * i + 2))";
   "word_add (word_add c (word (16 * i + 12))) (word 18446744073709551604):int64 = word_add c (word (16 * i))";
   "word_add (word_add c (word (16 * i + 12))) (word 18446744073709551608):int64 = word_add c (word (16 * i + 4))";
   "word_add (word_add c (word (16 * i + 12))) (word 18446744073709551612):int64 = word_add c (word (16 * i + 8))"];;

let PACKW1_STMT fn loop exit =
  parse_term(Printf.sprintf
  "exists f_events.
  forall e c op pc (x:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    ALL (nonoverlapping (op,192)) [(c,1024); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RAX s = word_add c (word 12) /\\ read R8 s = word 0 /\\
              read R13 s = word_add op (word 2) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add c (word (4*i)))) s = x i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read RAX s = word_add c (word 1036) /\\ read R8 s = word 192 /\\
              read R13 s = word_add op (word 2) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add c (word (4*i)))) s = x i) /\\
              (!j. j < 192 ==> read (memory :> bytes8 (word_add op (word j))) s = mld_polyw1_pack_88 x j) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events c op pc /\\
                 memaccess_inbounds e2 [c,1024; op,192] [op,192]))
         (MAYCHANGE [RIP; RAX; R8; RDX; RSI; RDI] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(op,192)])"
  image_mc fn loop fn exit);;

let PACKW1_TAC exec fn loop exit =
  CONCRETIZE_F_EVENTS_TAC
   `\(c:int64) (op:int64) (pc:num).
      APPEND (f_ev_epil c op pc)
       (APPEND (ENUMERATEL 64 (\i. f_ev_loop c op pc i)) (f_ev_prol c op pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `c:int64`; `op:int64`; `pc:num`; `x:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `64` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   `\i s. read RAX s = word_add c (word (16 * i + 12)) /\
          read R8 s = word (3 * i) /\
          read R13 s = word_add op (word 2) /\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add c (word(4 * j)))) s = x j) /\
          (!j. j < 3 * i
               ==> read(memory :> bytes8(word_add op (word j))) s = mld_polyw1_pack_88 x j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    CHUNK_INPUT_TAC `x:num->int32` 4 THEN
    INPUT_ALT_ADDR_TAC `c:int64` THEN
    VAL_INT64_TAC `3 * i` THEN
    ALIAS_ASSUME_TAC PACKW1_ALIASES THEN
    X86_STEPS_TAC exec (1--20) THEN
    CHUNK_FULL_FINAL_ARS_TAC [ARITH_RULE `3 * (i + 1) = 3 * i + 3`; ARITH_RULE `16 * (i + 1) = 16 * i + 16`] mld_polyw1_pack_88 `x:num->int32`;
    FULL_EXIT0_TAC];;

let PROVE_PACKW1 fn loop exit =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(PACKW1_STMT fn loop exit, PACKW1_TAC exec fn loop exit);;

(* ------------------------------------------------------------------------- *)
(* Abbreviations that the simulation keeps opaque: abbrev_def v t, for v = t *)
(* ------------------------------------------------------------------------- *)

let abbrev_def = new_definition `abbrev_def (x:A) (y:A) <=> x = y`;;

let abbrev_ctr = par_local_ref (fun () -> 0);;

(* After a step to state s, abbreviate the value of each 64-bit register and
   the low 128 bits of each 256-bit register (as word_join hi lo) that is not
   a variable or a numeral word by a fresh variable abN, with abbrev_def abN t,
   so that the terms of the next steps stay small. *)
let ABBREV_STATE_TAC (s:term) =
  let is_small t = is_var t ||
    (is_comb t && is_const(rator t) && fst(dest_const(rator t)) = "word" &&
     is_numeral(rand t)) in
  let gprs = ["RAX";"RBX";"RCX";"RDX";"RSI";"RDI";"R8";"R9";"R10";"R11";
              "R12";"R13";"R14";"R15"] in
  let one th =
    let c = concl th in
    if not (is_eq c) then ALL_TAC else
    let l = lhs c and r = rhs c in
    match l with
      Comb(Comb(Const("read",_),Const(reg,_)),st) when st = s ->
        let target =
          if String.length reg >= 3 && String.sub reg 0 3 = "YMM" then
            (match r with
               Comb(Comb(Const("word_join",_),_),lo) when not (is_small lo) ->
                 Some lo
             | _ -> None)
          else if mem reg gprs && not(is_small r) then Some r
          else None in
        (match target with
           None -> ALL_TAC
         | Some t ->
             incr (abbrev_ctr ());
             let v = mk_var("ab"^string_of_int (!(abbrev_ctr ())), type_of t) in
             let ex = mk_exists(v,mk_eq(t,v)) in
             MP_TAC(EXISTS (ex,t) (REFL t)) THEN
             DISCH_THEN(X_CHOOSE_THEN v (fun eth ->
               FIRST_X_ASSUM(fun th' -> if concl th' = c then
                   ASSUME_TAC(CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV
                     (fun t' -> if t' = t then eth else failwith ""))) th')
                 else NO_TAC) THEN
               ASSUME_TAC(EQ_MP (SYM(ISPECL [v;t] abbrev_def)) (SYM eth)))))
    | _ -> ALL_TAC in
  W(fun (asl,w) -> MAP_EVERY (fun (_,th) -> one th) asl);;

let ABBREV_STEPS_TAC execth ns =
  MAP_EVERY (fun n ->
    X86_STEPS_TAC execth [n] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO; VERIF_SUBWORD_JOIN_HI]) THEN
    ABBREV_STATE_TAC (mk_var("s"^string_of_int n,`:x86state`))) ns;;

(*** The equation v = t of the abbreviation named name ***)

let ABBREV_THM name (asl,w) =
  let th = snd(find (fun (_,th) ->
     match concl th with
       Comb(Comb(Const("abbrev_def",_),Var(n,_)),_) -> n = name
     | _ -> false) asl) in
  EQ_MP (ISPECL [lhand(concl th); rand(concl th)] abbrev_def) th;;

let UNFOLD_ABBREVS_TAC names =
  W(fun g -> REWRITE_TAC(map (fun n -> ABBREV_THM n g) names));;

let abn l = map (fun i -> "ab"^string_of_int i) l;;

(* ------------------------------------------------------------------------- *)
(* The comparison of c~ (cc0, cc1 at rsp0 + 64, + 80) with c2 (dd0, dd1 at   *)
(* rsp0 + 96, + 112), as clang 23 vectorizes mld_ct_memcmp: the OR of the    *)
(* differences folded to a byte d, and the result -6 unless d = 0, chosen    *)
(* by CMOVE (the XOR fold of the differences, in AL, cancels). From the      *)
(* return of the call of mld_H44 for c2 to the jump to join2.                *)
(* ------------------------------------------------------------------------- *)

let CMP44_STMT fn =
  parse_term(subst_tokens ["@FN@",fn; "@MC@",image_mc]
  "exists f_events.
  forall e rsp0 pc (cc0:int128) (cc1:int128) (dd0:int128) (dd1:int128).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    aligned 16 (word_add rsp0 (word 64)) /\\ aligned 16 (word_add rsp0 (word 96)) /\\
    ALL (nonoverlapping (word_add rsp0 (word 64),64)) [(word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) @MC@ /\\
              read RIP s = word (pc + @FN@_after_mld_H44_2) /\\
              read RSP s = rsp0 /\\
              read (memory :> bytes128 (word_add rsp0 (word 64))) s = cc0 /\\
              read (memory :> bytes128 (word_add rsp0 (word 80))) s = cc1 /\\
              read (memory :> bytes128 (word_add rsp0 (word 96))) s = dd0 /\\
              read (memory :> bytes128 (word_add rsp0 (word 112))) s = dd1 /\\
              read events s = e)
         (\\s. read RIP s = word (pc + @FN@_join2) /\\
              read RSP s = rsp0 /\\
              read R14 s = (if cc0 = dd0 /\\ cc1 = dd1 then word 0 else word 4294967290) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 pc /\\
                 memaccess_inbounds e2 [word_add rsp0 (word 64),64] []))
         (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; R14] ,, MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])");;

let CMP44_TAC execth =
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (pc:num). f_ev_all rsp0 pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `pc:num`;
    `cc0:int128`; `cc1:int128`; `dd0:int128`; `dd1:int128`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
  GHOST_INTRO_TAC `ymm2_init:int256` `read YMM2` THEN
  GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN
  GHOST_INTRO_TAC `ymm4_init:int256` `read YMM4` THEN
  FULL_INIT_TAC THEN
  MAP_EVERY (fun a ->
    FIRST_ASSUM(fun th ->
      if can (term_match [] (subst [mk_small_numeral a,`k:num`]
           `read (memory :> bytes128 (word_add rsp0 (word k))) s = x`)) (concl th)
      then MAP_EVERY STRIP_ASSUME_TAC [CONV_RULE(READ_MEMORY_SPLIT_CONV 1) th;
                                       CONV_RULE(READ_MEMORY_SPLIT_CONV 2) th]
      else NO_TAC)) [80; 112] THEN
  ADDR_NORMALIZE_TAC THEN
  (fun g -> abbrev_ctr () := 0; ALL_TAC g) THEN
  ABBREV_STEPS_TAC execth (1--59) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ab13:int128 = word_xor dd1 cc1` ASSUME_TAC THENL
   [UNFOLD_ABBREVS_TAC (abn [13;12;11;10;9;7;6;5;4;3;2]) THEN CONV_TAC WORD_BLAST;
    ALL_TAC] THEN
  SUBGOAL_THEN `ab49:int64 = if (word_zx (ab41:int64):byte) = word 0
                             then word 0 else word 4294967290` SUBST1_TAC THENL
   [UNFOLD_ABBREVS_TAC (abn [49;48;47;46;45]) THEN REWRITE_TAC[WORD_VAL_MOD_256] THEN
    CONV_TAC BITBLAST_RULE;
    ALL_TAC] THEN
  SUBGOAL_THEN `(word_zx (ab41:int64):byte = word 0) <=> (ab15:int128 = word 0)`
   SUBST1_TAC THENL
   [UNFOLD_ABBREVS_TAC (abn [41;40;39;38;37;36;35;34;33]) THEN
    REWRITE_TAC[WORD_VAL_MOD_256] THEN CONV_TAC BITBLAST_RULE;
    ALL_TAC] THEN
  UNFOLD_ABBREVS_TAC (abn [15;1]) THEN ASM_REWRITE_TAC[WORD_OR_EQ_0; WORD_XOR_EQ_0] THEN
  CONJ_TAC THENL
   [AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN MESON_TAC[];
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let PROVE_CMP44 fn =
  let execth = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_after_mld_H44_2"), layout fn + 0x1b04)] in
  prove(CMP44_STMT fn, CMP44_TAC execth);;

(* ------------------------------------------------------------------------- *)
(* The end of verify_internal, from join2 to the return: the memsets and the *)
(* SSE stores that zero the buffers in the frame of fr bytes at rsp0 (as the *)
(* region from rsp0 - 8, where the calls of memset push their return         *)
(* address), the restoring of RSP from RBP and of the six registers pushed  *)
(* at rb = RBP - 40, and the result, the low 32 bits of R14, in RAX.         *)
(* RUN_STRAIGHT_TAC simulates such straight-line code with the calls of      *)
(* memset through its contract (named memset_name), to the return. The      *)
(* addresses of the frame are offsets of the lowest, rsp0 - 8, so that the   *)
(* containment of the accesses is plain arithmetic, and the facts about the  *)
(* registers saved at rb are rewritten with the alias of the LEA of RSP.     *)
(* ------------------------------------------------------------------------- *)

let CL_STMT fn fr =
  let frs = string_of_int (fr + 8) in
  parse_term(subst_tokens ["@FN@",fn; "@FR8@",frs; "@MC@",image_mc]
  "!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e rsp0 rb r pc rbx0 r12_0 r13_0 r14_0 r15_0 rbp_0 ra.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          aligned 32 (rsp0:int64) /\\
          ALL (nonoverlapping (word_sub rsp0 (word 8),@FR8@))
              [(word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el);
               (rb,56)]
          ==> ensures x86
               (\\s. bytes_loaded s (word pc) @MC@ /\\
                    read RIP s = word (pc + @FN@_join2) /\\
                    read RSP s = rsp0 /\\ read RBP s = word_add rb (word 40) /\\
                    read R14 s = r /\\
                    read (memory :> bytes64 rb) s = rbx0 /\\
                    read (memory :> bytes64 (word_add rb (word 8))) s = r12_0 /\\
                    read (memory :> bytes64 (word_add rb (word 16))) s = r13_0 /\\
                    read (memory :> bytes64 (word_add rb (word 24))) s = r14_0 /\\
                    read (memory :> bytes64 (word_add rb (word 32))) s = r15_0 /\\
                    read (memory :> bytes64 (word_add rb (word 40))) s = rbp_0 /\\
                    read (memory :> bytes64 (word_add rb (word 48))) s = ra /\\
                    (read DF s <=> false) /\\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                    read (memory :> bytes(ea,el)) s = ev /\\
                    read events s = e)
               (\\s. read RIP s = ra /\\
                    read RSP s = word_add rb (word 56) /\\
                    read RAX s = word_zx(word_zx r:int32) /\\
                    read RBX s = rbx0 /\\ read R12 s = r12_0 /\\ read R13 s = r13_0 /\\
                    read R14 s = r14_0 /\\ read R15 s = r15_0 /\\ read RBP s = rbp_0 /\\
                    (exists e2. read events s = APPEND e2 e /\\
                       e2 = f_events (word_sub rsp0 (word 8)) rb mf pc ra /\\
                       memaccess_inbounds e2
                        [word_sub rsp0 (word 8),@FR8@; rb,48; word_add rb (word 48),8;
                         word(pc + got_memset),8; ea,el]
                        [word_sub rsp0 (word 8),@FR8@]))
               (MAYCHANGE [RSP; RBX; RBP; R12; R13; R14; R15] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(word_sub rsp0 (word 8),@FR8@)])");;

(* The offset n in the fact read RIP s = word n (with pc + n reduced to n by
   pc being a variable, -1 if the value is not of that form) *)
let cur_pc_offset (asl,w) =
  let s = rand w in
  try let t = rhs(concl(snd(find (fun (_,th) ->
        try lhs(concl th) = mk_comb(`read RIP`,s) with Failure _ -> false) asl))) in
      dest_small_numeral(rand(rand t))
  with Failure _ -> -1;;

(* RSP after a call through a contract is word_add (word_sub rsp (word 8))
   (word 8); unless it is rsp again, the addresses relative to RSP do not
   match the facts about the frame, and an aligned SSE store whose
   alignment is then unknown does not return. *)
let RSP_SUB_ADD_8 = WORD_RULE `word_add (word_sub (x:int64) (word 8)) (word 8) = x`;;
let RSP_NORM_TAC = RULE_ASSUM_TAC(REWRITE_RULE[RSP_SUB_ADD_8]);;

(* Simulate straight-line code with calls of memset through the PLT from
   state 0 until RIP is not an address in the image (after the return). *)
let RUN_STRAIGHT_TAC execth memset_name allowed =
  let plt = layout "plt_memset" and got = layout "got_memset" in
  let rec run n (asl,w) =
    let off = cur_pc_offset (asl,w) in
    if off = plt then
      (LIBC_PLT_TAC execth plt got (n - 1) THEN
       LIBC_FULL_CALL_TAC memset_name execth
        [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
         `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
        allowed (n + 1) THEN RSP_NORM_TAC THEN
       run (n + 2)) (asl,w)
    else if off < 0 then ALL_TAC (asl,w)
    else (X86_STEPS_TAC execth [n] THEN run (n + 1)) (asl,w) in
  run 1;;

let CL_ALIGNED_TAC offs =
  SUBGOAL_THEN `aligned 16 (word_add rsp0 (word 8):int64)` ASSUME_TAC THENL
   [MATCH_MP_TAC(MP (ISPECL [`16`;`32`;`word_add rsp0 (word 8):int64`] ALIGNED_WORD_WEAKEN)
                    (EQT_ELIM(DIVIDES_CONV `16 divides 32`))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY (fun off ->
    SUBGOAL_THEN (subst [mk_small_numeral (off+8),`n:num`]
                    `aligned 16 (word_add (rsp0:int64) (word n))`) ASSUME_TAC THENL
     [SUBST1_TAC(WORD_RULE(subst [mk_small_numeral (off+8),`n:num`; mk_small_numeral off,`m:num`]
        `word_add (rsp0:int64) (word n) = word_add (word_add rsp0 (word 8)) (word m)`)) THEN
      MATCH_MP_TAC ALIGNED_WORD_ADD THEN ASM_REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN
      REWRITE_TAC[];
      ALL_TAC]) offs;;

let CL_RUN_TAC fn fr aoffs =
  let execth = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_join2"), layout (fn^"_ret") + 1); layout_range "plt_memset"] in
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[memset_full_contract] th) "H_MEMSET") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (rb:int64) (mf:int64) (pc:num) (ra:int64).
      f_ev_all rsp0 rb mf pc ra:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  X_GEN_TAC `e:(uarch_event)list` THEN WORD_FORALL_OFFSET_TAC 8 THEN
  MAP_EVERY X_GEN_TAC [`rsp0:int64`; `rb:int64`; `r:int64`; `pc:num`;
    `rbx0:int64`; `r12_0:int64`; `r13_0:int64`; `r14_0:int64`; `r15_0:int64`; `rbp_0:int64`; `ra:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES; fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  CL_ALIGNED_TAC aoffs THEN
  ASSUME_TAC(prove(`word_add (word_add rb (word 40)) (word 18446744073709551576):int64 = rb`,
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[WORD_ADD_0])) THEN
  FULL_INIT_TAC THEN
  RUN_STRAIGHT_TAC execth "H_MEMSET"
    (ref [`rsp0:int64`; `rb:int64`; `mf:int64`; `pc:num`; `ra:int64`]);;

let CL_TAC fn fr aoffs =
  CL_RUN_TAC fn fr aoffs THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_VAL_ADD_64; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* fn: the function; fr: the size of its frame below the realigned RSP;
   aoffs: the offsets in it of the aligned SSE stores *)
let PROVE_CL fn fr aoffs = prove(CL_STMT fn fr, CL_TAC fn fr aoffs);;

(* ------------------------------------------------------------------------- *)
(* tr = SHAKE256(pk) as clang 23 inlines it into verify_internal (44): the   *)
(* state at a = rsp0 + 128 zeroed, the 9 full blocks of 136 bytes of the     *)
(* public key XORed in by SSE code, each followed by a call of               *)
(* mldsa_keccakf1600_permute, the last 88 bytes XORed in as 11 lanes, the    *)
(* padding bytes 0x1F and 0x80, and the last permutation, whose state the    *)
(* code then copies out. The proof keeps the state as a 1600-bit word        *)
(* between the calls (mld_keccak_absorb_blocks of the blocks so far), splits *)
(* it into the chunks and lanes that the code reads (inline_sponge_b.ml),    *)
(* and merges them after the XOR (TR_BLK_MERGE, TR_FIN_MERGE). The state and *)
(* the block are named by variables during the simulation of a block, so     *)
(* that it does not evaluate 2 EXP 1088 in them. The frame is stated from    *)
(* fb = rsp0 - 296, the bottom of the stack of the permutation.              *)
(* ------------------------------------------------------------------------- *)


(* chunks of a byte array given as a number, at any byte offset *)
let TR_CHUNK_OF_NUM n =
  let sub = subst_tokens ["@N@",string_of_int n; "@NB@",string_of_int (n/8);
                          "@BN@",Printf.sprintf "bytes%d" n] in
  let wth = (match n with 8 -> BYTES8_WBYTES | 16 -> BYTES16_WBYTES | 32 -> BYTES32_WBYTES
             | 64 -> BYTES64_WBYTES | _ -> BYTES128_WBYTES) in
  prove(parse_term(sub
   "!(a:int64) m x k (s:x86state).
        read (memory :> bytes(a,m)) s = x /\\ k + @NB@ <= m
        ==> read (memory :> @BN@ (word_add a (word k))) s =
            word((x DIV 2 EXP (8 * k)) MOD 2 EXP @N@)"),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `m:num`; `x:num`; `k:num`; parse_term(sub "@NB@"); `s:x86state`]
    READ_MEMORY_BYTES_SUB) THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[wth; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_MOD_REFL] THEN DISCH_THEN ACCEPT_TAC);;

let TR_CHUNK128_OF_NUM = TR_CHUNK_OF_NUM 128;;
let TR_CHUNK64_OF_NUM = TR_CHUNK_OF_NUM 64;;

(* the subwords of block k of the message as a 1600-bit word *)
let TR_BLK_SUB = prove
 (`!PK k p n. p + n <= 1088 /\ n = dimindex(:N)
        ==> (word_subword (word((PK DIV 2 EXP (1088 * k)) MOD 2 EXP 1088):1600 word)
                          (p,n):N word) =
            word((PK DIV 2 EXP (1088 * k + p)) MOD 2 EXP n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_subword; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  SUBGOAL_THEN `((PK DIV 2 EXP (1088 * k)) MOD 2 EXP 1088) MOD 2 EXP 1600 =
                (PK DIV 2 EXP (1088 * k)) MOD 2 EXP 1088` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN TRANS_TAC LTE_TRANS `2 EXP 1088` THEN
    REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ; LE_EXP] THEN ARITH_TAC;
    ALL_TAC] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  SUBGOAL_THEN `MIN (1088 * k + 1088) (1088 * k + p + n) = 1088 * k + p + n`
   SUBST1_TAC THENL [ASM_ARITH_TAC; REFL_TAC]);;

let TR_HI_ZERO = prove
 (`!PK k p n. PK < 2 EXP 10496 /\ 10496 <= 1088 * k + p
        ==> (word_subword (word((PK DIV 2 EXP (1088 * k)) MOD 2 EXP 1088):1600 word)
                          (p,n):N word) = word 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_subword; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(MESON[MOD_0] `!x n. x = 0 ==> x MOD n = 0`) THEN
  SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
  TRANS_TAC LET_TRANS `PK DIV 2 EXP (1088 * k)` THEN CONJ_TAC THENL
   [MESON_TAC[MOD_LE; LE_TRANS];
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
    TRANS_TAC LTE_TRANS `2 EXP 10496` THEN ASM_REWRITE_TAC[LE_EXP] THEN
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The absorbing of the public key into the Keccak state at a = rsp0 + 128   *)
(* (tr = SHAKE256(pk) in verify_internal), for 44: the state zeroed, 9 full  *)
(* blocks of 136 bytes XORed in with SSE code and permuted by calls of       *)
(* mldsa_keccakf1600_permute, the last 88 bytes XORed in as 11 lanes, the    *)
(* padding bytes 0x1F and 0x80, and the last permutation. The frame is       *)
(* stated from fb = rsp0 - 296 (the frame of the permutation and its return  *)
(* address), so that the region is fb + [0, 632); the code changes only the  *)
(* stack of the permutation and the 208 bytes of the state, so that what the *)
(* caller keeps in rsp0 .. rsp0 + 127 survives.                              *)
(* ------------------------------------------------------------------------- *)

let TR_NORM_CONV =
  DEPTH_CONV(NUM_MULT_CONV ORELSEC NUM_ADD_CONV) THENC
  REWRITE_CONV[CONJUNCT1 EXP; DIV_1; WORD_ADD_0];;

let TR_NORM_RULE = CONV_RULE(TR_NORM_CONV THENC
                             ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV);;

(* MP of th, whose antecedent is a conjunction, with fact for the first
   conjunct and the second decided by arithmetic on numerals *)
let tr_num_true t =
  EQT_ELIM((DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) t);;
let tr_mp_conj th fact =
  let a = lhand(concl th) in MP th (CONJ fact (tr_num_true (rand a)));;
let tr_mp_num th = MP th (tr_num_true(lhand(concl th)));;

(*** The block word WB k and the state before block k ***)

let tr_wb k =
  let t = if k = 0 then `word(PK MOD 2 EXP 1088):1600 word`
          else subst [mk_small_numeral(1088 * k),`n:num`]
                 `word((PK DIV 2 EXP n) MOD 2 EXP 1088):1600 word` in
  t;;

let tr_st k =
  if k = 0 then `word 0:1600 word`
  else subst [mk_small_numeral k,`k:num`]
        `mld_keccak_absorb_blocks 136 (word 0) PK k`;;

(*** The state at a as chunks: 128-bit chunks j < 8, lanes n of 64 bits ***)

let TR_STATE_CHUNKS_TAC (a:term) (chunks:int list) (lanes:int list) =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && can (term_match [] `read (memory :> wbytes x) (s:x86state)`) (lhs c) &&
       rand(rand(rand(rator(lhs c)))) = a
    then
      let s = rand(lhs c) and x = rhs c in
      MAP_EVERY (fun j ->
        ASSUME_TAC(TR_NORM_RULE(tr_mp_conj (SPECL [a; x; mk_small_numeral j; s]
          READ_MEMORY_BYTES128_OF_WBYTES) th))) chunks THEN
      MAP_EVERY (fun n ->
        ASSUME_TAC(TR_NORM_RULE(tr_mp_conj (SPECL [a; x; mk_small_numeral n; s]
          READ_MEMORY_BYTES64_OF_WBYTES) th))) lanes
    else NO_TAC);;

(*** The facts for the loads of block k of the key at pk: 128-bit chunks j ***)
(*** at 136 k + 16 j and 64-bit lanes n at 136 k + 8 n, as subwords of WB  ***)

let TR_PK_TAC (k:int) (chunks:int list) (lanes:int list) =
  let wb = tr_wb k in
  let one bits off pos =
    FIRST_ASSUM(fun th ->
      let c = concl th in
      if is_eq c && can (term_match [] `read (memory :> bytes(pk,1312)) (s:x86state)`) (lhs c)
      then
        let s = rand(lhs c) in
        let lem = if bits = 128 then TR_CHUNK128_OF_NUM else TR_CHUNK64_OF_NUM in
        let th1 = TR_NORM_RULE(tr_mp_conj
                    (SPECL [`pk:int64`; `1312`; `PK:num`; mk_small_numeral off; s] lem) th) in
        let ty = if bits = 128 then `:128` else `:64` in
        let th2 = TR_NORM_RULE(tr_mp_num (INST_TYPE [ty,`:N`]
                    (SPECL [`PK:num`; mk_small_numeral k; mk_small_numeral pos; mk_small_numeral bits]
                     TR_BLK_SUB))) in
        ASSUME_TAC(TRANS th1 (SYM th2))
      else NO_TAC) in
  MAP_EVERY (fun j -> one 128 (136 * k + 16 * j) (128 * j)) chunks THEN
  MAP_EVERY (fun n -> one 64 (136 * k + 8 * n) (64 * n)) lanes;;

(*** A byte of a state given as a word ***)

let TR_BYTE_OF_WBYTES = prove
 (`!(a:int64) (X:1600 word) k (s:x86state).
        read (memory :> wbytes a) s = X /\ k < 200
        ==> read (memory :> bytes8 (word_add a (word k))) s =
            word_subword X (8 * k,8)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `200`; `val(X:1600 word)`; `k:num`; `s:x86state`]
    (TR_CHUNK_OF_NUM 8)) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
      CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE];
      ASM_ARITH_TAC];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[word_subword]]);;

(*** The state after XORing a full block W into the state S ***)

let TR_BLK_MERGE = prove
 (`!(a:int64) (S:1600 word) (W:1600 word) (s:x86state).
     (!j. j < 8
          ==> read (memory :> bytes128 (word_add a (word (16 * j)))) s =
              word_xor (word_subword W (128 * j,128)) (word_subword S (128 * j,128))) /\
     read (memory :> bytes64 (word_add a (word 128))) s =
     word_xor (word_subword S (1024,64)) (word_subword W (1024,64)) /\
     (!n. n < 8
          ==> read (memory :> bytes64 (word_add a (word (136 + 8 * n)))) s =
              word_subword S (1088 + 64 * n,64)) /\
     (!n. n < 8 ==> word_subword W (1088 + 64 * n,64) = (word 0:int64))
     ==> read (memory :> wbytes a) s = word_xor S W`,
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV EXPAND_CASES_CONV)) THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV) THENC
                     REWRITE_CONV[WORD_ADD_0])) THEN
  STRIP_TAC THEN
  MATCH_MP_TAC READ_MEMORY_WBYTES_OF_LANES THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN
  MAP_EVERY (fun j ->
    FIRST_ASSUM(fun th ->
      let c = concl th in
      if is_eq c && can (term_match [] `read (memory :> bytes128 x) (s:x86state)`) (lhs c) &&
         (let ad = rand(rand(rand(rator(lhs c)))) in
          ad = (if j = 0 then `a:int64` else
                subst [mk_small_numeral(16 * j),`n:num`] `word_add (a:int64) (word n)`))
      then let th' = MATCH_MP READ_MEMORY_BYTES64_OF_BYTES128 th in
           STRIP_ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th')
      else NO_TAC)) (0--7) THEN
  ASM_REWRITE_TAC[WORD_SUBWORD_XOR; WORD_XOR_0] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

(*** The state after the last 88 bytes W and the padding bytes ***)

let TR_FIN_MERGE = prove
 (`!(a:int64) (S:1600 word) (W:1600 word) (s:x86state).
  (!n. n < 11 ==> read (memory :> bytes64 (word_add a (word (8 * n)))) s =
                  word_xor (word_subword S (64 * n,64)) (word_subword W (64 * n,64))) /\
  read (memory :> bytes8 (word_add a (word 88))) s =
  word_xor (word_subword S (704,8)) (word 31) /\
  (!m. m < 7 ==> read (memory :> bytes8 (word_add a (word (89 + m)))) s =
                 word_subword S (712 + 8 * m,8)) /\
  (!n. n < 4 ==> read (memory :> bytes64 (word_add a (word (96 + 8 * n)))) s =
                 word_subword S (768 + 64 * n,64)) /\
  (!m. m < 7 ==> read (memory :> bytes8 (word_add a (word (128 + m)))) s =
                 word_subword S (1024 + 8 * m,8)) /\
  read (memory :> bytes8 (word_add a (word 135))) s =
  word_xor (word_subword S (1080,8)) (word 128) /\
  (!n. n < 8 ==> read (memory :> bytes64 (word_add a (word (136 + 8 * n)))) s =
                 word_subword S (1088 + 64 * n,64)) /\
  (!n. n < 14 ==> word_subword W (704 + 64 * n,64) = (word 0:int64))
  ==> read (memory :> wbytes a) s =
      word_xor (word_xor (word_xor S W) (word(2 EXP 704 * 31)))
               (word(2 EXP 1080 * 128))`,
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV EXPAND_CASES_CONV)) THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV) THENC
                     REWRITE_CONV[WORD_ADD_0])) THEN
  STRIP_TAC THEN
  MATCH_MP_TAC READ_MEMORY_WBYTES_OF_LANES THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN
  MAP_EVERY (fun k ->
    let t = subst [mk_small_numeral k,`k:num`]
              `read (memory :> bytes64 (word_add (a:int64) (word k))) (s:x86state)` in
    GEN_REWRITE_TAC (ONCE_DEPTH_CONV o LAND_CONV)
     [CONV_RULE(RAND_CONV(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV))
                 (READ_MEMORY_MERGE_CONV 3 t)]) [88; 128] THEN
  ASM_REWRITE_TAC[WORD_SUBWORD_XOR; WORD_XOR_0] THEN
  CONV_TAC(NUM_REDUCE_CONV THENC WORD_REDUCE_CONV) THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

(*** The zeroed state ***)

let TR_ZERO_MERGE = prove
 (`!(a:int64) (s:x86state).
     (!j. j < 12 ==> read (memory :> bytes128 (word_add a (word (16 * j)))) s = word 0) /\
     read (memory :> bytes32 (word_add a (word 192))) s = word 0 /\
     read (memory :> bytes32 (word_add a (word 196))) s = word 0
     ==> read (memory :> wbytes a) s = (word 0:1600 word)`,
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV EXPAND_CASES_CONV)) THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV NUM_MULT_CONV THENC REWRITE_CONV[WORD_ADD_0])) THEN
  STRIP_TAC THEN
  MATCH_MP_TAC READ_MEMORY_WBYTES_OF_LANES THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[WORD_ADD_0; WORD_SUBWORD_0] THEN
  MAP_EVERY (fun j ->
    FIRST_ASSUM(fun th ->
      let c = concl th in
      if is_eq c && can (term_match [] `read (memory :> bytes128 x) (s:x86state)`) (lhs c) &&
         (let ad = rand(rand(rand(rator(lhs c)))) in
          ad = (if j = 0 then `a:int64` else
                subst [mk_small_numeral(16 * j),`n:num`] `word_add (a:int64) (word n)`))
      then let th' = MATCH_MP READ_MEMORY_BYTES64_OF_BYTES128 th in
           STRIP_ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th')
      else NO_TAC)) (0--11) THEN
  GEN_REWRITE_TAC (ONCE_DEPTH_CONV o LAND_CONV)
   [CONV_RULE(RAND_CONV(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV))
     (READ_MEMORY_MERGE_CONV 1
       `read (memory :> bytes64 (word_add (a:int64) (word 192))) (s:x86state)`)] THEN
  ASM_REWRITE_TAC[WORD_SUBWORD_0] THEN CONV_TAC WORD_BLAST);;

(*** mld_shake256_state of the key as the code computes it ***)

let TR44_STATE_EQ = prove
 (`!PK. mld_shake256_state 1312 PK =
        word_xor (word_xor (word_xor (mld_keccak_absorb_blocks 136 (word 0) PK 9)
                                     (word((PK DIV 2 EXP 9792) MOD 2 EXP 1088)))
                           (word(2 EXP 704 * 31)))
                 (word(2 EXP 1080 * 128))`,
  REWRITE_TAC[mld_shake256_state; mld_keccak_absorb; mld_keccak_finalize] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV ORELSEC NUM_DIV_CONV ORELSEC
                      NUM_MOD_CONV ORELSEC NUM_SUB_CONV)) THEN
  REWRITE_TAC[CONJUNCT1 EXP; MULT_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(*** One permutation step of the absorbing ***)

let TR_BLOCKS_STEP k =
  let th0 = INST [`136`,`r:num`; `word 0:1600 word`,`S:1600 word`; `PK:num`,`X:num`;
                 mk_small_numeral k,`n:num`]
              (CONJUNCT2 mld_keccak_absorb_blocks) in
  let th1 = CONV_RULE(LAND_CONV(RAND_CONV NUM_SUC_CONV) THENC
                      RAND_CONV(DEPTH_CONV NUM_MULT_CONV THENC
                                REWRITE_CONV[CONJUNCT1 EXP; DIV_1;
                                             CONJUNCT1 mld_keccak_absorb_blocks])) th0 in
  SYM th1;;

let TR_WB_HI = prove
 (`!x p. 1088 <= p ==> word_subword (word (x MOD 2 EXP 1088):1600 word) (p,64):int64 = word 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_subword; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  SUBGOAL_THEN `(x MOD 2 EXP 1088) MOD 2 EXP 1600 DIV 2 EXP p = 0`
   (fun th -> REWRITE_TAC[th; MOD_0]) THEN
  SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
  MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 1088` THEN
  ASM_REWRITE_TAC[LE_EXP; ARITH_EQ] THEN
  MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `x MOD 2 EXP 1088` THEN
  REWRITE_TAC[MOD_LE; MOD_LT_EQ; EXP_EQ_0; ARITH_EQ]);;

(*** The statement ***)

let TR44_STMT fn =
  parse_term(subst_tokens ["@FN@",fn; "@MC@",image_mc;
                           "@START@",string_of_int(layout fn + 0x4fb)]
  "exists f_events.
   forall e rsp0 pk pc PK.
     aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
     aligned 32 (rsp0:int64) /\\
     ALL (nonoverlapping (word_sub rsp0 (word 296),632))
         [(word pc,libmldsa_size); (pk,1312)]
     ==> ensures x86
          (\\s. bytes_loaded s (word pc) @MC@ /\\
               read RIP s = word (pc + @START@) /\\
               read RSP s = rsp0 /\\ read RBX s = pk /\\
               read (memory :> bytes(pk,1312)) s = PK /\\
               read events s = e)
          (\\s. read RIP s = word (pc + @FN@_after_mldsa_keccakf1600_permute_10) /\\
               read RSP s = rsp0 /\\ read RBX s = pk /\\
               read R15 s = word_add rsp0 (word 128) /\\
               read (memory :> wbytes (word_add rsp0 (word 128))) s =
               keccak_f1600 (mld_shake256_state 1312 PK) /\\
               (exists e2. read events s = APPEND e2 e /\\
                  e2 = f_events (word_sub rsp0 (word 296)) pk pc /\\
                  memaccess_inbounds e2
                   [pk,1312; word_sub rsp0 (word 296),632;
                    word(pc + rodata_mld_KeccakF_RoundConstants),192]
                   [word_sub rsp0 (word 296),632]))
          (MAYCHANGE [RSP; R15] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub rsp0 (word 296),296);
                      memory :> bytes(word_add rsp0 (word 128),208)])");;

let TR_ALIGNED_TAC base offs =
  SUBGOAL_THEN (subst [mk_small_numeral base,`b:num`]
                 `aligned 16 (word_add fb (word b):int64)`) ASSUME_TAC THENL
   [MATCH_MP_TAC(MP (ISPECL [`16`;`32`;subst [mk_small_numeral base,`b:num`]
                    `word_add fb (word b):int64`] ALIGNED_WORD_WEAKEN)
                    (EQT_ELIM(DIVIDES_CONV `16 divides 32`))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY (fun off ->
    SUBGOAL_THEN (subst [mk_small_numeral (off+base),`n:num`]
                    `aligned 16 (word_add (fb:int64) (word n))`) ASSUME_TAC THENL
     [SUBST1_TAC(WORD_RULE(subst [mk_small_numeral (off+base),`n:num`;
                                  mk_small_numeral off,`m:num`; mk_small_numeral base,`b:num`]
        `word_add (fb:int64) (word n) = word_add (word_add fb (word b)) (word m)`)) THEN
      MATCH_MP_TAC ALIGNED_WORD_ADD THEN ASM_REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN
      REWRITE_TAC[];
      ALL_TAC]) offs;;

(*** The antecedents of the merge lemmas from the facts ***)

let TR_ANTE_TAC =
  REPEAT CONJ_TAC THEN
  CONV_TAC(DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(TR_NORM_CONV THENC ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  REPEAT CONJ_TAC THEN
  FIRST [ASM_REWRITE_TAC[WORD_SUBWORD_0; WORD_XOR_0; VERIF_SUBWORD_JOIN_LO; VERIF_SUBWORD_JOIN_HI] THEN NO_TAC;
         MATCH_MP_TAC TR_WB_HI THEN CONV_TAC NUM_REDUCE_CONV;
         MATCH_MP_TAC TR_HI_ZERO THEN
         ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV];;

let tr_fb_add n = subst [mk_small_numeral n,`n:num`] `word_add (fb:int64) (word n)`;;

(*** A variable v for the term t: abbrev_def v t, and t replaced by v in ***)
(*** the assumptions (so that the simulation does not reduce t)          ***)

let TR_NAME_TAC (t:term) (vname:string) =
  let v = mk_var(vname,type_of t) in
  let ex = mk_exists(v,mk_eq(t,v)) in
  MP_TAC(EXISTS (ex,t) (REFL t)) THEN
  DISCH_THEN(X_CHOOSE_THEN v (fun eth ->
    RULE_ASSUM_TAC(REWRITE_RULE[eth]) THEN
    ASSUME_TAC(EQ_MP (SYM(ISPECL [v;t] abbrev_def)) (SYM eth))));;

let TR_ABBREV_EQ vname (asl,w) =
  let th = snd(find (fun (_,th) ->
     match concl th with
       Comb(Comb(Const("abbrev_def",_),Var(n,_)),_) -> n = vname
     | _ -> false) asl) in
  EQ_MP (ISPECL [lhand(concl th); rand(concl th)] abbrev_def) th;;

let TR_UNNAME_GOAL_TAC vname = W(fun g -> REWRITE_TAC[TR_ABBREV_EQ vname g]);;

let TR_UNNAME_TAC (vname:string) =
  FIRST_X_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("abbrev_def",_),Var(n,_)),_) when n = vname ->
        let eq = EQ_MP (ISPECL [lhand(concl th); rand(concl th)] abbrev_def) th in
        RULE_ASSUM_TAC(REWRITE_RULE[eq])
    | _ -> NO_TAC);;

(*** One full block k: from the state after the call (or the zeroing) at  ***)
(*** step n0 to the call of the permutation, with the result rewritten    ***)
(*** as the absorbing of k + 1 blocks                                     ***)

let TR_BLOCK_TAC execth k n0 =
  let a = tr_fb_add 424 in
  let nsteps = if k = 0 then 25 else 28 in
  let ncall = n0 + nsteps + 1 in
  let sn = mk_var("s"^string_of_int(n0 + nsteps),`:x86state`) in
  let sv = if k = 0 then tr_st 0 else mk_var("st"^string_of_int k,`:1600 word`)
  and wv = mk_var("wb"^string_of_int k,`:1600 word`) in
  TR_STATE_CHUNKS_TAC a (0--7) (16--24) THEN
  TR_PK_TAC k (0--7) [16] THEN
  (if k = 0 then ALL_TAC else TR_NAME_TAC (tr_st k) ("st"^string_of_int k)) THEN
  TR_NAME_TAC (tr_wb k) ("wb"^string_of_int k) THEN
  X86_STEPS_TAC execth ((n0+1)--(n0+nsteps)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO; VERIF_SUBWORD_JOIN_HI]) THEN
  MP_TAC(SPECL [a; sv; wv; sn] TR_BLK_MERGE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL
     [ALL_TAC; TR_UNNAME_GOAL_TAC ("wb"^string_of_int k)]]] THEN
    TR_ANTE_TAC;
    DISCH_TAC] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc execth "H_PERM"
   [`read RDI s`; mk_comb(mk_comb(`word_xor:1600 word->1600 word->1600 word`,sv),wv);
    `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   [`fb:int64`; `pk:int64`; `pc:num`] ncall THEN
  (if k = 0 then ALL_TAC else TR_UNNAME_TAC ("st"^string_of_int k)) THEN
  TR_UNNAME_TAC ("wb"^string_of_int k) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TR_BLOCKS_STEP k]) THEN
  YMM_GHOST_TAC (mk_var("s"^string_of_int ncall,`:x86state`))
   ["YMM0","y0_"^string_of_int k; "YMM1","y1_"^string_of_int k];;

(*** Bytes k of the state at a ***)

let TR_STATE_BYTES_TAC (a:term) (ks:int list) =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && can (term_match [] `read (memory :> wbytes x) (s:x86state)`) (lhs c) &&
       rand(rand(rand(rator(lhs c)))) = a
    then
      let s = rand(lhs c) and x = rhs c in
      MAP_EVERY (fun k ->
        ASSUME_TAC(TR_NORM_RULE(tr_mp_conj (SPECL [a; x; mk_small_numeral k; s]
          TR_BYTE_OF_WBYTES) th))) ks
    else NO_TAC);;

(*** The last block of 88 bytes, the padding and the last permutation, from ***)
(*** the state after the call at step n0                                    ***)

let TR44_FINAL_TAC execth n0 =
  let a = tr_fb_add 424 in
  let sv = mk_var("st9",`:1600 word`) and wv = mk_var("wb9",`:1600 word`) in
  let sn = mk_var("s"^string_of_int(n0 + 27),`:x86state`) in
  let fin = list_mk_icomb "word_xor"
             [list_mk_icomb "word_xor"
               [list_mk_icomb "word_xor" [sv; wv]; `word(2 EXP 704 * 31):1600 word`];
              `word(2 EXP 1080 * 128):1600 word`] in
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes(pk,1312)) (s:x86state) = PK`) (concl th)
    then let st = rand(lhs(concl th)) in
         let b = ISPECL [`pk:int64`; `1312`;
                         mk_comb(`read memory:x86state->int64->byte`,st)] READ_BYTES_BOUND in
         ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
                     (REWRITE_RULE[GSYM READ_COMPONENT_COMPOSE; th] b))
    else NO_TAC) THEN
  TR_STATE_CHUNKS_TAC a [] ((0--10) @ (12--15) @ (17--24)) THEN
  TR_STATE_BYTES_TAC a ((88--95) @ (128--135)) THEN
  TR_PK_TAC 9 [] (0--10) THEN
  TR_NAME_TAC (tr_st 9) "st9" THEN TR_NAME_TAC (tr_wb 9) "wb9" THEN
  X86_STEPS_TAC execth ((n0+1)--(n0+27)) THEN
  MP_TAC(SPECL [a; sv; wv; sn] TR_FIN_MERGE) THEN
  ANTS_TAC THENL
   [REPEAT(CONJ_TAC THENL [TR_ANTE_TAC; ALL_TAC]) THEN
    TR_UNNAME_GOAL_TAC "wb9" THEN
    CONV_TAC(DEPTH_CONV EXPAND_CASES_CONV) THEN CONV_TAC TR_NORM_CONV THEN
    REPEAT CONJ_TAC THEN
    MATCH_MP_TAC(TR_NORM_RULE(SPECL [`PK:num`; `9`] TR_HI_ZERO)) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    DISCH_TAC] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc execth "H_PERM"
   [`read RDI s`; fin; `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   [`fb:int64`; `pk:int64`; `pc:num`] (n0 + 28) THEN
  TR_UNNAME_TAC "st9" THEN TR_UNNAME_TAC "wb9" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM TR44_STATE_EQ]);;

let TR44_TAC fn =
  let execth = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout fn + 0x4fb, layout (fn^"_after_mldsa_keccakf1600_permute_10"))] in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERM" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(fb:int64) (pk:int64) (pc:num). f_ev_all fb pk pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  X_GEN_TAC `e:(uarch_event)list` THEN WORD_FORALL_OFFSET_TAC 296 THEN
  MAP_EVERY X_GEN_TAC [`fb:int64`; `pk:int64`; `pc:num`; `PK:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  TR_ALIGNED_TAC 296 [0x80;0x90;0xa0;0xb0;0xc0;0xd0;0xe0;0xf0;0x100;0x110;0x120;0x130] THEN
  GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
  FULL_INIT_TAC THEN
  X86_STEPS_TAC execth (1--2) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes128 (word_add fb (word 612))) s2 = x`)
           (concl th)
    then STRIP_ASSUME_TAC(CONV_RULE(READ_MEMORY_SPLIT_CONV 2) th) else NO_TAC) THEN
  ADDR_NORMALIZE_TAC THEN
  X86_STEPS_TAC execth (3--14) THEN
  MP_TAC(SPECL [tr_fb_add 424; `s14:x86state`] TR_ZERO_MERGE) THEN
  ANTS_TAC THENL [TR_ANTE_TAC; DISCH_TAC] THEN
  TR_BLOCK_TAC execth 0 14 THEN
  MAP_EVERY (fun k -> TR_BLOCK_TAC execth k (40 + 29 * (k - 1))) (1--8) THEN
  TR44_FINAL_TAC execth 272 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let PROVE_TR44 fn = prove(TR44_STMT fn, TR44_TAC fn);;

(* ------------------------------------------------------------------------- *)
(* The loops of the unpacking of the hints of polynomial i (mld_sig_unpack_  *)
(* hints, 44: omega = 80, k = 4, the hint bytes b at sig + 2336) as clang 23 *)
(* inlines it into verify_internal: L1 sets the coefficient of each position *)
(* after the first (which the code peels), failing at the first byte that is *)
(* not greater than the one before; L2 checks that the unused bytes of the   *)
(* last polynomial are zero, failing at the first that is not. Both leave    *)
(* the loop early on failure, so their counts (cl_n1, cl_n2) and exit (join7 *)
(* or join8, else join1) depend on the bytes, as in the gcc glue of          *)
(* utils/mldsa_native_hints.ml whose counts and lemmas they use.             *)
(*                                                                           *)
(* RIP_DECIDE_TAC decides a conditional branch from the arithmetic facts     *)
(* about the numbers that it compares, keeping the arithmetic small (only    *)
(* the facts about its variables); BYTE_IDX_DISCHARGE_TAC lets the memory-   *)
(* safety check of a store at an address indexed by a byte use the bound    *)
(* of the byte, which CONTAINED_TAC cannot see through val.                  *)
(* ------------------------------------------------------------------------- *)

let WORD_ADD1_64 = prove
 (`!n. word_add (word n) (word 1):int64 = word (n + 1)`, REWRITE_TAC[WORD_ADD]);;

let WORD_EQ_SMALL64 = prove
 (`!a b. a < 2 EXP 64 /\ b < 2 EXP 64 ==> (word a:int64 = word b <=> a = b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT]);;

let VAL_WORD_SMALL64 = prove
 (`!a. a < 2 EXP 64 ==> val(word a:int64) = a`,
  SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_LT]);;

(* The condition c of the fact read RIP s = if c then x else y, simplified with
   the bounds bnds (n < 2^64 for the numbers n of the words compared, proved
   by arithmetic from the assumptions), and decided by arithmetic from the
   assumptions about the numbers in it if possible *)
(* Prove the arithmetic fact c from the arithmetic assumptions whose free
   variables are among those of c (to keep the problem small) *)
let LOCAL_ARITH_RULE (asl:(string*thm) list) w =
  let fs = frees w in
  let isrel t = let t' = if is_neg t then rand t else t in
    (is_eq t' || is_binary "<" t' || is_binary "<=" t') &&
    (try type_of(lhand t') = `:num` with Failure _ -> false) in
  let rel = filter (fun th -> let t = concl th in isrel t && fs <> [] &&
                      subset (frees t) fs) (map snd asl) in
  let tm = itlist (curry mk_imp o concl) rel w in
  rev_itlist (C MP) rel (ARITH_RULE tm);;

let LOCAL_ARITH_TAC (asl,w) = ACCEPT_TAC(LOCAL_ARITH_RULE asl w) (asl,w);;

let BYTE_ZX3 = WORD_BLAST `word_zx (word_zx (word_zx (x:byte):int32):int64):byte = x`;;

let RIP_DECIDE_TAC (bnds:term list) =
  let isrip th = let c = concl th in
    is_eq c && can (term_match [] `read RIP s`) (lhs c) && is_cond(rhs c) in
  let isev th = let c = concl th in
    is_eq c && can (term_match [] `read events s`) (lhs c) in
  MAP_EVERY (fun n ->
    SUBGOAL_THEN (mk_binop `(<):num->num->bool` n `2 EXP 64`) ASSUME_TAC THENL
     [LOCAL_ARITH_TAC; ALL_TAC]) bnds THEN
  W(fun (asl,w) ->
    let bths = map (fun n -> snd(find (fun (_,th) ->
                 concl th = mk_binop `(<):num->num->bool` n `2 EXP 64`) asl)) bnds in
    RULE_ASSUM_TAC(fun th -> if isrip th || isev th then
       REWRITE_RULE[VAL_EQ_0; WORD_SUB_EQ_0; WORD_SUB_0]
        (SIMP_RULE (bths @ [VAL_WORD_SMALL64; WORD_EQ_SMALL64])
          (REWRITE_RULE[WORD_ADD1_64; GSYM ADD_ASSOC; WORD_VAL_MOD_256; BYTE_ZX3;
                        GLUE_CF_LEMMA; GLUE_ZF_LEMMA] th))
       else th)) THEN
  W(fun (asl,w) ->
    if not(exists (fun (_,th) -> isrip th) asl) then ALL_TAC else
    let th = snd(find (fun (_,th) -> isrip th) asl) in
    let c = rand(rator(rator(rhs(concl th)))) in
    let tryp c = LOCAL_ARITH_RULE asl c in
    (try let pth = tryp c in
         RULE_ASSUM_TAC(fun t -> if isrip t || isev t then REWRITE_RULE[EQT_INTRO pth] t else t)
     with Failure _ ->
     try let nth = tryp (mk_neg c) in
         RULE_ASSUM_TAC(fun t -> if isrip t || isev t then REWRITE_RULE[EQF_INTRO nth] t else t)
     with Failure _ -> ALL_TAC));;

(* For the memory-safety checks of accesses at byte-indexed addresses: each
   val x (x a byte) in the goal is generalized to a variable with the bound
   v < 256, which the arithmetic of CONTAINED_TAC can use (it ignores the
   assumptions that mention val). Used as memaccess_inbounds_normalize_tac. *)
let VAL_BYTE_GEN_TAC =
  W(fun (asl,w) ->
    let ts = setify(find_terms (fun t ->
      is_comb t && is_const(rator t) && fst(dest_const(rator t)) = "val" &&
      type_of(rand t) = `:byte` && not(is_var(rand t))) w) in
    MAP_EVERY (fun t ->
      let v = genvar `:num` in
      MP_TAC(ISPEC (rand t) GLUE_VAL_BYTE) THEN SPEC_TAC(t,v) THEN
      GEN_TAC THEN DISCH_TAC) ts);;

let BYTE_IDX_DISCHARGE_TAC tac =
  fun g ->
    memaccess_inbounds_normalize_tac := VAL_BYTE_GEN_TAC;
    try let r = tac g in memaccess_inbounds_normalize_tac := ALL_TAC; r
    with e -> memaccess_inbounds_normalize_tac := ALL_TAC; raise e;;

(* ------------------------------------------------------------------------- *)
(* The model of the check of the unused hint bytes of the last polynomial   *)
(* as clang 23 compiles it: for j from w (the count of the hints up to the  *)
(* last polynomial) to omega - 1, fail at the first nonzero byte. The loop  *)
(* runs cl_n2 omega b w times: omega - w if all the bytes are zero          *)
(* (cl_zeros), else up to and with the first nonzero byte, cl_m2.           *)
(* ------------------------------------------------------------------------- *)

let cl_zeros = new_definition
 `cl_zeros omega (b:num->byte) w <=> !j. w <= j /\ j < omega ==> b j = word 0`;;

let cl_m2 = new_definition
 `cl_m2 omega (b:num->byte) w =
    minimal j. w <= j /\ (j = omega \/ ~(b j = word 0))`;;

let cl_n2 = new_definition
 `cl_n2 omega (b:num->byte) w =
    if cl_zeros omega b w then omega - w else (cl_m2 omega b w - w) + 1`;;

let CL_N2 = prove
 (`!omega (b:num->byte) w.
     w < omega
     ==> 0 < cl_n2 omega b w /\
         (!p. p + 1 < cl_n2 omega b w ==> w + p + 1 < omega /\ b(w + p) = word 0) /\
         (cl_zeros omega b w ==> w + cl_n2 omega b w = omega /\
                                 b(w + cl_n2 omega b w - 1) = word 0) /\
         (~cl_zeros omega b w ==> w + cl_n2 omega b w <= omega /\
                                  ~(b(w + cl_n2 omega b w - 1) = word 0))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[cl_n2; cl_m2] THEN
  ASM_CASES_TAC `cl_zeros omega (b:num->byte) w` THEN ASM_REWRITE_TAC[] THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[cl_zeros]) THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      REPEAT STRIP_TAC THENL [ASM_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
      ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?j. w <= j /\ (j = omega \/ ~((b:num->byte) j = word 0))` MP_TAC THENL
   [EXISTS_TAC `omega:num` THEN ASM_SIMP_TAC[LT_IMP_LE]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [MINIMAL] THEN BETA_TAC THEN
  ABBREV_TAC `m = minimal j. w <= j /\ (j = omega \/ ~((b:num->byte) j = word 0))` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `~(m:num = omega)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~cl_zeros omega (b:num->byte) w` THEN
    REWRITE_TAC[cl_zeros] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (is_forall o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[DE_MORGAN_THM] THEN
    SUBGOAL_THEN `~(j:num = omega)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `m < omega` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `omega:num` o check (is_forall o concl)) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((b:num->byte) m = word 0)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w + p:num` o check (is_forall o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[DE_MORGAN_THM; LE_ADD] THEN
    SUBGOAL_THEN `~(w + p = omega)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    SUBGOAL_THEN `w + (m - w + 1) - 1 = m` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]]);;

let L2_STMT fn omega sh =
  parse_term(subst_tokens ["@FN@",fn; "@MC@",image_mc; "@OM@",string_of_int omega;
                           "@HB@",string_of_int(omega+ (if omega = 80 then 4 else if omega = 55 then 6 else 8));
                           "@SH@",string_of_int sh]
  "exists f_events.
   forall e sig w pc (b:num->byte).
     aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\ w < @OM@
     ==> ensures x86
          (\\s. bytes_loaded s (word pc) @MC@ /\\
               read RIP s = word (pc + @FN@_loop10) /\\
               read R8 s = sig /\\ read RAX s = word w /\\
               (!j. j < @HB@ ==> read (memory :> bytes8 (word_add sig (word (@SH@ + j)))) s = b j) /\\
               read events s = e)
          (\\s. read RIP s = word (if cl_zeros @OM@ b w then pc + @FN@_join8 else pc + @FN@_join1) /\\
               read R8 s = sig /\\
               (!j. j < @HB@ ==> read (memory :> bytes8 (word_add sig (word (@SH@ + j)))) s = b j) /\\
               (exists e2. read events s = APPEND e2 e /\\ e2 = f_events sig w pc b /\\
                  memaccess_inbounds e2 [word_add sig (word @SH@),@HB@] []))
          (MAYCHANGE [RIP; RAX] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])");;


(* Decide the conditions of the conditionals in the goal that are equations
   or inequalities of numbers (not under a binder), by arithmetic from the
   assumptions *)
let NUM_ADD_EQ_CONV tm =
  match tm with
    Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),x),a)),b)
      when is_numeral a && is_numeral b && not(is_numeral x) ->
        let an = dest_numeral a and bn = dest_numeral b in
        if Num.le_num an bn then
          ARITH_RULE(mk_eq(tm,mk_eq(x,mk_numeral(Num.sub_num bn an))))
        else ARITH_RULE(mk_eq(tm,`F`))
  | _ -> failwith "NUM_ADD_EQ_CONV";;

(* Decide the conditions of the conditionals in the goal that are equations
   or inequalities of numbers (not under a binder), by arithmetic from the
   arithmetic assumptions about their variables *)
let DECIDE_NUM_CONDS_TAC =
  let rec conds bound t =
    match t with
      Comb(Comb(Comb(Const("COND",_),c),x),y) ->
        (if intersect (frees c) bound = [] then [c] else []) @
        conds bound c @ conds bound x @ conds bound y
    | Comb(f,x) -> conds bound f @ conds bound x
    | Abs(v,b) -> conds (v::bound) b
    | _ -> [] in
  let isnumrel c =
    let c' = if is_neg c then rand c else c in
    (is_eq c' || is_binary "<" c' || is_binary "<=" c') &&
    type_of(lhand c') = `:num` &&
    not(can (find_term (fun t -> is_const t &&
      let n = fst(dest_const t) in
      String.length n > 3 && (String.sub n 0 3 = "cl_" || String.sub n 0 4 = "glue"))) c') in
  let prover c (asl,w) =
    let fs = frees c in
    let rel = filter (fun th -> let t = concl th in isnumrel t &&
                        subset (frees t) fs && not(fs = [])) (map snd asl) in
    let tm = itlist (curry mk_imp o concl) rel c in
    ACCEPT_TAC(rev_itlist (C MP) rel (ARITH_RULE tm)) (asl,w) in
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_EQ_CONV) THEN
  W(fun (asl,w) ->
    let cs = setify(filter isnumrel (conds [] w)) in
    MAP_EVERY (fun c ->
      TRY((SUBGOAL_THEN c (fun th -> REWRITE_TAC[EQT_INTRO th]) THENL
            [prover c; ALL_TAC]) ORELSE
          (SUBGOAL_THEN (mk_neg c) (fun th -> REWRITE_TAC[EQF_INTRO th]) THENL
            [prover (mk_neg c); ALL_TAC]))) cs);;

let L2_TAC execth fn =
  let j8 = mk_small_numeral(layout(fn^"_join8"))
  and j1 = mk_small_numeral(layout(fn^"_join1"))
  and lp = mk_small_numeral(layout(fn^"_loop10")) in
  let pcp n = mk_binop `(+):num->num->num` `pc:num` n in
  let path_end =
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ADD1_64] THEN
    LOOP_TEST_TAC THEN
    DECIDE_NUM_CONDS_TAC THEN
    REPEAT CONJ_TAC THEN
    TRY(REWRITE_TAC[ADD_ASSOC] THEN NO_TAC) THEN
    TRY(ASM_REWRITE_TAC[GSYM ADD_ASSOC] THEN NO_TAC) THEN
    PATH_DISCHARGE_TAC in
  CONCRETIZE_F_EVENTS_TAC
   `\(sig:int64) (w:num) (pc:num) (b:num->byte).
      APPEND (f_ev_epil sig w pc b)
       (APPEND (ENUMERATEL (cl_n2 80 b w)
          (\p. if p + 1 < cl_n2 80 b w then f_ev_it sig w pc b p
               else if cl_zeros 80 b w then f_ev_ok sig w pc b p
               else f_ev_bad sig w pc b p))
        (f_ev_prol sig w pc b)) :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `sig:int64`; `w:num`; `pc:num`; `b:num->byte`] THEN
  REWRITE_TAC[SOME_FLAGS; fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`80`; `b:num->byte`; `w:num`] CL_N2) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `w + cl_n2 80 b w <= 80` ASSUME_TAC THENL
   [ASM_CASES_TAC `cl_zeros 80 (b:num->byte) w` THEN ASM_MESON_TAC[LE_REFL]; ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `cl_n2 80 b w` (pcp lp)
   (mk_cond(`cl_zeros 80 b w`,pcp j8,pcp j1))
   `\p s. read R8 s = sig /\
          (p < cl_n2 80 b w \/ cl_zeros 80 b w ==> read RAX s = word (w + p)) /\
          (!j. j < 84 ==> read (memory :> bytes8 (word_add sig (word (2336 + j)))) s = b j)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `w + p < 80` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `p + 1 < cl_n2 80 b w` THENL
     [FIRST_ASSUM(MP_TAC o SPEC `p:num` o check (fun th ->
        is_forall(concl th) && free_in `cl_n2` (concl th))) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC];
      SUBGOAL_THEN `w + cl_n2 80 b w - 1 = w + p` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_CASES_TAC `cl_zeros 80 (b:num->byte) w` THENL
       [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
          lhand(concl th) = `cl_zeros 80 (b:num->byte) w`)) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        SUBGOAL_THEN `w + p + 1 = 80` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC];
        FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
          lhand(concl th) = `~cl_zeros 80 (b:num->byte) w`)) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC]] THEN
    (FULL_INIT_TAC THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `2336`)) (concl th)
       then MP_TAC(SPEC `w + p:num` th) else NO_TAC) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    VAL_INT64_TAC `w + p:num` THEN
    ALIAS_ASSUME_TAC ["word_add sig (word (1 * (w + p) + 2336)):int64 = word_add sig (word (2336 + w + p))"] THEN
    X86_STEPS_TAC execth (1--2) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUB_0; VAL_EQ_0]) THEN
    ASM_REWRITE_TAC[] THEN
    (fun g -> if can (find_term (fun t -> t = `~((b:num->byte)(w + p) = word 0)`)) (snd g) ||
                 exists (fun (_,th) -> concl th = `~((b:num->byte)(w + p) = word 0)`) (fst g)
              then ALL_TAC g else X86_STEPS_TAC execth (3--5) g) THEN
    path_end);
    FULL_EXIT0_TAC];;

let PROVE_L2 fn =
  let execth = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_loop10"), layout (fn^"_join8"))] in
  prove(L2_STMT fn 80 2336, L2_TAC execth fn);;

(* ------------------------------------------------------------------------- *)
(* The loop over the hint positions j = s + 1 + p of polynomial i after the  *)
(* first (clang 23 peels it): it fails at the first j whose byte is not      *)
(* greater than the one before, and sets the coefficient b j otherwise, up   *)
(* to j = w - 1. It runs cl_n1 times: n1 - 1 if the bytes increase (ok1),    *)
(* else n1, the last iteration failing (n1 = glue_suh_n1).                   *)
(* ------------------------------------------------------------------------- *)

let cl_n1 = new_definition
 `cl_n1 omega (b:num->byte) i =
    if glue_suh_ok1 omega b i then glue_suh_n1 omega b i - 1
    else glue_suh_n1 omega b i`;;

let L1_STMT fn =
  parse_term(subst_tokens ["@FN@",fn; "@MC@",image_mc]
  "exists f_events.
   forall e sig rsp0 pc (b:num->byte) i.
     aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
     ~glue_suh_early 80 b i /\\
     mld_hints_start 80 b i + 1 < glue_suh_new 80 b i /\\
     nonoverlapping (word_add rsp0 (word 1248),1024) (word pc,libmldsa_size) /\\
     nonoverlapping (word_add rsp0 (word 1248),1024) (word_add sig (word 2336),84)
     ==> ensures x86
          (\\s. bytes_loaded s (word pc) @MC@ /\\
               read RIP s = word (pc + @FN@_join13) /\\
               read RSP s = rsp0 /\\ read R8 s = sig /\\
               read RAX s = word (mld_hints_start 80 b i) /\\
               read RBX s = word (glue_suh_new 80 b i) /\\
               (!j. j < 84 ==> read (memory :> bytes8 (word_add sig (word (2336 + j)))) s = b j) /\\
               (!q. q < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (1248 + 4 * q)))) s =
                                glue_suh_h 80 b i 1 q) /\\
               read events s = e)
          (\\s. read RIP s = word (if glue_suh_ok1 80 b i then pc + @FN@_join7 else pc + @FN@_join1) /\\
               read RSP s = rsp0 /\\ read R8 s = sig /\\
               read RAX s = word (mld_hints_start 80 b i) /\\
               read RBX s = word (glue_suh_new 80 b i) /\\
               (!j. j < 84 ==> read (memory :> bytes8 (word_add sig (word (2336 + j)))) s = b j) /\\
               (glue_suh_ok1 80 b i
                ==> !q. q < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (1248 + 4 * q)))) s =
                                    mld_unpack_hints 80 b i q) /\\
               (exists e2. read events s = APPEND e2 e /\\ e2 = f_events sig rsp0 pc b i /\\
                  memaccess_inbounds e2 [word_add sig (word 2336),84; word_add rsp0 (word 1248),1024]
                                        [word_add rsp0 (word 1248),1024]))
          (MAYCHANGE [RIP; RDX; RSI; RDI; R10] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(word_add rsp0 (word 1248),1024)])");;

let BYTE_ZX2_VAL = prove
 (`!x:byte. val(word_zx (word_zx x:int32):int64) = val x`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
  MP_TAC(ISPEC `x:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT; ARITH_RULE `x < 256 ==> x < 4294967296`;
    ARITH_RULE `x < 256 ==> x < 18446744073709551616`]);;

let WORD_ADD_M1_64 = prove
 (`!w. 1 <= w ==> word_add (word w) (word 18446744073709551615):int64 = word (w - 1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN
  SUBGOAL_THEN `w + 18446744073709551615 = (w - 1) + 18446744073709551616` SUBST1_TAC THENL
   [ASM_ARITH_TAC;
    REWRITE_TAC[WORD_ADD; WORD_REDUCE_CONV `word 18446744073709551616:int64`; WORD_ADD_0]]);;

let L1_TAC execth fn =
  let lbl l = mk_small_numeral(layout(fn^"_"^l)) in
  let pcp n = mk_binop `(+):num->num->num` `pc:num` n in
  let s_ = `mld_hints_start 80 (b:num->byte) i` and w_ = `glue_suh_new 80 (b:num->byte) i` in
  let j = `mld_hints_start 80 (b:num->byte) i + p + 1` in
  let bnds = [`mld_hints_start 80 (b:num->byte) i + p + 1`; s_;
              `glue_suh_new 80 (b:num->byte) i - 1`] in
  let common_pre =
    FULL_INIT_TAC THEN
    MAP_EVERY (fun t ->
      FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `2336`)) (concl th)
         then MP_TAC(SPEC t th) else NO_TAC) THEN
      ANTS_TAC THENL [LOCAL_ARITH_TAC; DISCH_TAC])
     [`mld_hints_start 80 (b:num->byte) i + p`; j] THEN
    VAL_INT64_TAC `mld_hints_start 80 (b:num->byte) i + p` THEN
    ALIAS_ASSUME_TAC
     ["word_add sig (word (1 * (mld_hints_start 80 b i + p) + 2337)):int64 = word_add sig (word (2336 + mld_hints_start 80 b i + p + 1))";
      "word_add sig (word (1 * (mld_hints_start 80 b i + p) + 2336)):int64 = word_add sig (word (2336 + mld_hints_start 80 b i + p))"] THEN
    X86_STEPS_TAC execth (1--4) THEN RIP_DECIDE_TAC bnds THEN
    X86_STEPS_TAC execth (5--6) THEN RIP_DECIDE_TAC bnds in
  let store_tac =
    FIRST_ASSUM(fun th ->
      if is_forall(concl th) && free_in `glue_suh_h` (concl th) then
        ASSUME_TAC(TAC_PROOF(([],subst [j,`j:num`]
          `!q. q < 256 /\ ~(q = val((b:num->byte) j))
               ==> read(memory :> bytes32(word_add rsp0 (word(1248 + 4 * q)))) s6 =
                   glue_suh_h 80 b i (p + 1) q`),
          REPEAT STRIP_TAC THEN MATCH_MP_TAC th THEN ASM_REWRITE_TAC[]))
      else NO_TAC) THEN
    ASSUME_TAC(SPEC (mk_comb(`b:num->byte`,j)) GLUE_VAL_BYTE) THEN
    ASSUME_TAC(ISPEC (mk_comb(`b:num->byte`,j)) BYTE_ZX2_VAL) THEN
    ALIAS_ASSUME_TAC ["word_add rsp0 (word (4 * val ((b:num->byte) (mld_hints_start 80 b i + p + 1)) + 1248)):int64 = word_add rsp0 (word (1248 + 4 * val ((b:num->byte) (mld_hints_start 80 b i + p + 1))))"] THEN
    X86_STEPS_TAC execth (7--10) THEN RIP_DECIDE_TAC bnds in
  let h_tac =
    X_GEN_TAC `q:num` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GLUE_SUH_H_ADD1] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]] in
  let path_end =
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ADD1_64] THEN
    REPEAT CONJ_TAC THEN
    TRY(REWRITE_TAC[GSYM ADD_ASSOC] THEN NO_TAC) THEN
    TRY(ASM_REWRITE_TAC[GSYM ADD_ASSOC] THEN NO_TAC) THEN
    TRY(h_tac THEN NO_TAC) THEN
    TRY(FIRST_X_ASSUM(fun th -> if can (find_term (fun t -> is_const t && fst(dest_const t) = "MAYCHANGE")) (concl th) &&
                                 not(is_imp(concl th)) then MP_TAC th else NO_TAC) THEN
        VAL_BYTE_GEN_TAC THEN DISCH_TAC THEN MONOTONE_MAYCHANGE_TAC THEN NO_TAC) THEN
    BYTE_IDX_DISCHARGE_TAC PATH_DISCHARGE_TAC in
  CONCRETIZE_F_EVENTS_TAC
   `\(sig:int64) (rsp0:int64) (pc:num) (b:num->byte) (i:num).
      APPEND (f_ev_epil sig rsp0 pc b i)
       (APPEND (ENUMERATEL (cl_n1 80 b i)
          (\p. if p + 1 < cl_n1 80 b i then f_ev_it sig rsp0 pc b i p
               else if glue_suh_ok1 80 b i then f_ev_ok sig rsp0 pc b i p
               else f_ev_bad sig rsp0 pc b i p))
        (f_ev_prol sig rsp0 pc b i)) :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `sig:int64`; `rsp0:int64`; `pc:num`;
                       `b:num->byte`; `i:num`] THEN
  REWRITE_TAC[SOME_FLAGS; fst execth; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`80`; `b:num->byte`; `i:num`] GLUE_SUH_N1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC(SPECL [`80`; `b:num->byte`; `i:num`] GLUE_SUH_BOUNDS) THEN
  SUBGOAL_THEN `glue_suh_new 80 (b:num->byte) i <= 80` ASSUME_TAC THENL
   [UNDISCH_TAC `~glue_suh_early 80 (b:num->byte) i` THEN
    REWRITE_TAC[glue_suh_early] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `0 < cl_n1 80 (b:num->byte) i /\
                mld_hints_start 80 b i + cl_n1 80 b i + 1 <= glue_suh_new 80 b i /\
                cl_n1 80 b i <= glue_suh_n1 80 b i`
   STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[cl_n1] THEN COND_CASES_TAC THENL
     [SUBGOAL_THEN `mld_hints_start 80 b i + glue_suh_n1 80 b i = glue_suh_new 80 b i`
       MP_TAC THENL [ASM_MESON_TAC[]; ASM_ARITH_TAC];
      FIRST_ASSUM(MP_TAC o C MP (ASSUME `~glue_suh_ok1 80 (b:num->byte) i`) o
        check (fun th -> is_imp(concl th) && is_neg(lhand(concl th)))) THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= glue_suh_new 80 (b:num->byte) i` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_iff(concl th) && lhand(concl th) = `glue_suh_ok1 80 (b:num->byte) i`
    then ASSUME_TAC(fst(EQ_IMP_RULE th)) else NO_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `cl_n1 80 b i` (pcp (lbl "join15"))
   (mk_cond(`glue_suh_ok1 80 b i`,pcp (lbl "join7"),pcp (lbl "join1")))
   `\p s. read RSP s = rsp0 /\ read R8 s = sig /\
          read RAX s = word (mld_hints_start 80 b i) /\
          read RBX s = word (glue_suh_new 80 b i) /\
          read R10 s = word (glue_suh_new 80 b i - 1) /\
          (!j. j < 84 ==> read (memory :> bytes8 (word_add sig (word (2336 + j)))) s = b j) /\
          (p < cl_n1 80 b i \/ glue_suh_ok1 80 b i
           ==> read RDX s = word (mld_hints_start 80 b i + p) /\
               (!q. q < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (1248 + 4 * q)))) s =
                                glue_suh_h 80 b i (p + 1) q))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    FULL_INIT_TAC THEN X86_STEPS_TAC execth (1--3) THEN
    RULE_ASSUM_TAC(fun th -> try REWRITE_RULE[MATCH_MP WORD_ADD_M1_64
       (ASSUME `1 <= glue_suh_new 80 (b:num->byte) i`)] th with Failure _ -> th) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `p + 1 < cl_n1 80 b i` THENL
     [FIRST_ASSUM(MP_TAC o SPEC `p:num` o check (fun th ->
        is_forall(concl th) && free_in `glue_suh_n1` (concl th) &&
        free_in `val:byte->num` (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
      common_pre THEN store_tac THEN path_end;
      ASM_CASES_TAC `glue_suh_ok1 80 (b:num->byte) i` THENL
       [SUBGOAL_THEN `mld_hints_start 80 b i + cl_n1 80 b i + 1 = glue_suh_new 80 b i /\
                      p + 1 < glue_suh_n1 80 b i` STRIP_ASSUME_TAC THENL
         [SUBGOAL_THEN `mld_hints_start 80 b i + glue_suh_n1 80 b i = glue_suh_new 80 b i /\
                        cl_n1 80 b i = glue_suh_n1 80 b i - 1` MP_TAC THENL
           [REWRITE_TAC[cl_n1] THEN ASM_SIMP_TAC[]; ASM_ARITH_TAC];
          ALL_TAC] THEN
        FIRST_ASSUM(MP_TAC o SPEC `p:num` o check (fun th ->
          is_forall(concl th) && free_in `glue_suh_n1` (concl th) &&
          free_in `val:byte->num` (concl th))) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
        common_pre THEN store_tac THEN path_end;
        SUBGOAL_THEN `mld_hints_start 80 b i + glue_suh_n1 80 b i =
                      mld_hints_start 80 b i + p + 1 /\
                      (mld_hints_start 80 b i + glue_suh_n1 80 b i) - 1 =
                      mld_hints_start 80 b i + p` STRIP_ASSUME_TAC THENL
         [SUBGOAL_THEN `cl_n1 80 b i = glue_suh_n1 80 b i` MP_TAC THENL
           [REWRITE_TAC[cl_n1] THEN ASM_REWRITE_TAC[]; ASM_ARITH_TAC];
          ALL_TAC] THEN
        FIRST_ASSUM(MP_TAC o C MP (ASSUME `~glue_suh_ok1 80 (b:num->byte) i`) o
          check (fun th -> is_imp(concl th) && is_neg(lhand(concl th)))) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        common_pre THEN X86_STEPS_TAC execth (7--7) THEN path_end]];
    REWRITE_TAC[LT_REFL] THEN FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(DISCH_TAC THEN
        SUBGOAL_THEN `mld_hints_start 80 b i + cl_n1 80 b i + 1 = glue_suh_new 80 b i`
         ASSUME_TAC THENL
         [SUBGOAL_THEN `mld_hints_start 80 b i + glue_suh_n1 80 b i = glue_suh_new 80 b i /\
                        cl_n1 80 b i = glue_suh_n1 80 b i - 1` MP_TAC THENL
           [REWRITE_TAC[cl_n1] THEN ASM_SIMP_TAC[]; ASM_ARITH_TAC];
          ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
          free_in `glue_suh_h` (concl th))) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        X_GEN_TAC `q:num` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `q:num` o check (fun th -> is_forall (concl th) &&
          free_in `glue_suh_h` (concl th))) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        MATCH_MP_TAC GLUE_SUH_H_FULL THEN ASM_ARITH_TAC THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let PROVE_L1 fn =
  let execth = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_join13"), layout (fn^"_join15") + 0x21)] in
  prove(L1_STMT fn, L1_TAC execth fn);;


(* ------------------------------------------------------------------------- *)
(* The unpacking of the hints of polynomial i in verify_internal (44), from  *)
(* the exit of the caddq loop (loop9_exit) to their use at join11, or to     *)
(* join1 if they are malformed. The code reads the counts s and w of the     *)
(* hints before and up to polynomial i (bytes 80 + i - 1 and 80 + i of the   *)
(* hints) and fails if s > w or w > 80 (glue_suh_early); it zeroes the 1024  *)
(* bytes of the coefficients with memset, sets the coefficient of the first  *)
(* hint and runs the loop L1 over the others, which fails if the positions   *)
(* do not grow (glue_suh_ok1); for the last polynomial it runs the loop L2,  *)
(* which fails if a byte after the hints is not zero. The region is split    *)
(* into four segments with ENSURES_EVENTS_SEQUENCE_TAC: to after_memset_7,   *)
(* to join7, to join8 and to join11 (each starting at join1 instead if the   *)
(* segment before failed, where HZ_SKIP_TAC ends it with no steps). Two      *)
(* lessons from it: the theorems of the region lemmas used inside (L1, L2)   *)
(* must be assumed before the template of the events is made concrete, as    *)
(* those of the callees, since the instantiated template refers to their     *)
(* event functions; and in a segment after the first, the events of the      *)
(* segments before are in the precondition, so SEG_DISCHARGE_TAC splits the  *)
(* memory-safety goal and that assumption over the APPENDs.                  *)
(* ------------------------------------------------------------------------- *)

let HZ_ZERO32_0 = prove
 (`!(a:int64) (s:x86state).
     (!i. i < 1024 ==> read (memory :> bytes8 (word_add a (word i))) s = word 0)
     ==> !q. q < 256 ==> read (memory :> bytes32 (word_add a (word (4 * q)))) s = word 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`word_add a (word (4 * q)):int64`; `4`; `(\j. word 0):num->byte`; `s:x86state`]
    READ_BYTES_OF_BYTES8) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV(RAND_CONV(REWRITE_CONV[num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`;
                                             list_of_seq; num_of_bytelist; APPEND; VAL_WORD_0] THENC
                               NUM_REDUCE_CONV))) THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0; BYTES32_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  SIMP_TAC[]);;

let HZ_ZERO32 = prove
 (`!(a:int64) k (s:x86state).
     (!i. i < 1024 ==> read (memory :> bytes8 (word_add a (word (k + i)))) s = word 0)
     ==> !q. q < 256 ==> read (memory :> bytes32 (word_add a (word (k + 4 * q)))) s = word 0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`word_add a (word k):int64`; `s:x86state`] HZ_ZERO32_0) THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN ASM_REWRITE_TAC[]);;

let BYTE_ZX1_VAL = prove
 (`(!x:byte. val(word_zx x:int32) = val x) /\
   (!x:byte. val(word_zx x:int64) = val x)`,
  CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
  MP_TAC(ISPEC `x:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT; ARITH_RULE `x < 256 ==> x < 4294967296`;
    ARITH_RULE `x < 256 ==> x < 18446744073709551616`]);;

let HINTS44_STMT fn =
  parse_term(subst_tokens ["@FN@",fn; "@MC@",image_mc]
  "!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e sig rsp0 pc (b:num->byte) i zp t1p.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\ i < 4 /\\
          ALL (nonoverlapping (rsp0,2272))
              [(word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el);
               (word_add sig (word 2336),84)] /\\
          ALL (nonoverlapping (word_sub rsp0 (word 8),8))
              [(word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el);
               (word_add sig (word 2336),84)]
          ==> ensures x86
               (\\s. bytes_loaded s (word pc) @MC@ /\\
                    read RIP s = word (pc + @FN@_loop9_exit) /\\
                    read RSP s = rsp0 /\\ read R15 s = zp /\\ read RBX s = t1p /\\
                    read (memory :> bytes64 (word_add rsp0 (word 40))) s = word i /\\
                    read (memory :> bytes64 (word_add rsp0 (word 56))) s = sig /\\
                    (!j. j < 84 ==> read (memory :> bytes8 (word_add sig (word (2336 + j)))) s = b j) /\\
                    (read DF s <=> false) /\\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                    read (memory :> bytes(ea,el)) s = ev /\\
                    read events s = e)
               (\\s. read RIP s = word (if mld_unpack_hints_ok 80 4 b i
                                       then pc + @FN@_join11 else pc + @FN@_join1) /\\
                    read RSP s = rsp0 /\\
                    read (memory :> bytes64 (word_add rsp0 (word 40))) s = word i /\\
                    read (memory :> bytes64 (word_add rsp0 (word 56))) s = sig /\\
                    (!j. j < 84 ==> read (memory :> bytes8 (word_add sig (word (2336 + j)))) s = b j) /\\
                    (read DF s <=> false) /\\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                    read (memory :> bytes(ea,el)) s = ev /\\
                    (mld_unpack_hints_ok 80 4 b i
                     ==> read RAX s = word 0 /\\ read R8 s = word 0 /\\ read R9 s = word 43 /\\
                         read RCX s = word i /\\
                         read R14 s = word_add rsp0 (word 2272) /\\ read R15 s = zp /\\
                         read RBX s = t1p /\\
                         (!q. q < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (1248 + 4 * q)))) s =
                                          mld_unpack_hints 80 b i q)) /\\
                    (exists e2. read events s = APPEND e2 e /\\
                       e2 = f_events rsp0 sig pc b i mf /\\
                       memaccess_inbounds e2
                        [rsp0,2272; word_sub rsp0 (word 8),8; word_add sig (word 2336),84;
                         word(pc + got_memset),8; ea,el]
                        [rsp0,2272; word_sub rsp0 (word 8),8]))
               (MAYCHANGE [RSP; RBX; R14; R15] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(word_add rsp0 (word 48),8);
                           memory :> bytes(word_add rsp0 (word 1248),1024);
                           memory :> bytes(word_sub rsp0 (word 8),8)])");;

let HINTS44_TEMPLATE =
  `\(rsp0:int64) (sig:int64) (pc:num) (b:num->byte) (i:num) (mf:int64).
    APPEND (if mld_unpack_hints_ok 80 4 b i then f_ev_c rsp0 sig pc b i mf
            else f_ev_cs rsp0 sig pc b i mf)
    (APPEND (if glue_suh_early 80 b i \/ ~glue_suh_ok1 80 b i then f_ev_bs rsp0 sig pc b i mf
             else if i = 3 then
               (if glue_suh_new 80 b i < 80
                then (if cl_zeros 80 b (glue_suh_new 80 b i) then f_ev_bz rsp0 sig pc b i mf
                      else f_ev_bnz rsp0 sig pc b i mf)
                else f_ev_bw rsp0 sig pc b i mf)
             else f_ev_bn rsp0 sig pc b i mf)
    (APPEND (if glue_suh_early 80 b i then f_ev_ms rsp0 sig pc b i mf
             else if mld_hints_start 80 b i < glue_suh_new 80 b i
             then (if mld_hints_start 80 b i + 1 < glue_suh_new 80 b i
                   then f_ev_ml rsp0 sig pc b i mf else f_ev_mq rsp0 sig pc b i mf)
             else f_ev_me rsp0 sig pc b i mf)
     (if glue_suh_early 80 b i
      then (if 0 < i then (if 80 < glue_suh_new 80 b i then f_ev_x1 rsp0 sig pc b i mf
                           else f_ev_x2 rsp0 sig pc b i mf)
            else f_ev_x0 rsp0 sig pc b i mf)
      else (if 0 < i then f_ev_p1 rsp0 sig pc b i mf else f_ev_p0 rsp0 sig pc b i mf))))
   :(uarch_event)list`;;

let HINTS_FRAME =
  "read RSP s = rsp0 /\\ read R14 s = zp /\\
   read (memory :> bytes64 (word_add rsp0 (word 40))) s = word i /\\
   read (memory :> bytes64 (word_add rsp0 (word 56))) s = sig /\\
   read (memory :> bytes64 (word_add rsp0 (word 48))) s = t1p /\\
   (!j. j < 84 ==> read (memory :> bytes8 (word_add sig (word (2336 + j)))) s = b j) /\\
   (read DF s <=> false) /\\
   read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
   read (memory :> bytes(ea,el)) s = ev";;

let HINTS_INV_A = parse_term("\\s. " ^ HINTS_FRAME ^ " /\\
   (~glue_suh_early 80 b i ==>
      read R15 s = word (mld_hints_start 80 b i) /\\
      read RBX s = word (glue_suh_new 80 b i) /\\
      (!q. q < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (1248 + 4 * q)))) s = word 0))");;

let HINTS_INV_B = parse_term("\\s. " ^ HINTS_FRAME ^ " /\\
   (~(glue_suh_early 80 b i \\/ ~glue_suh_ok1 80 b i) ==>
      read RCX s = word i /\\ read RBX s = word (glue_suh_new 80 b i) /\\
      read R8 s = sig /\\ read R9 s = word 43 /\\
      (!q. q < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (1248 + 4 * q)))) s =
                       mld_unpack_hints 80 b i q))");;

let HINTS_INV_C = parse_term("\\s. " ^ HINTS_FRAME ^ " /\\
   (mld_unpack_hints_ok 80 4 b i ==>
      read RCX s = word i /\\ read R15 s = zp /\\ read R9 s = word 43 /\\
      (!q. q < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (1248 + 4 * q)))) s =
                       mld_unpack_hints 80 b i q))");;

(* The callees (memset) and the region lemmas used (L1, L2) are assumed
   before the template of the events, whose functions are then instantiated
   with terms in their event functions. *)
let HINTS_SETUP_TAC fn l1th l2th t1a t1b t2 t3 =
  let lbl l = mk_small_numeral(layout(fn^"_"^l)) in
  let pcp n = mk_binop `(+):num->num->num` `pc:num` n in
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[memset_full_contract] th) "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC l1th "H_L1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC l2th "H_L2" THEN
  CONCRETIZE_F_EVENTS_TAC HINTS44_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `sig:int64`; `rsp0:int64`; `pc:num`;
    `b:num->byte`; `i:num`; `zp:int64`; `t1p:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  STRIP_ASSUME_TAC(SPECL [`80`; `b:num->byte`; `i:num`] GLUE_SUH_BOUNDS) THEN
  ENSURES_EVENTS_SEQUENCE_TAC
   (mk_cond(`mld_unpack_hints_ok 80 4 b i`,pcp (lbl "join8"),pcp (lbl "join1")))
   HINTS_INV_C THEN CONJ_TAC THENL
   [ENSURES_EVENTS_SEQUENCE_TAC
     (mk_cond(`glue_suh_early 80 b i \/ ~glue_suh_ok1 80 b i`,pcp (lbl "join1"),pcp (lbl "join7")))
     HINTS_INV_B THEN CONJ_TAC THENL
     [ENSURES_EVENTS_SEQUENCE_TAC
       (mk_cond(`glue_suh_early 80 b i`,pcp (lbl "join1"),pcp (lbl "after_memset_7")))
       HINTS_INV_A THEN CONJ_TAC THENL [t1a; t1b];
      t2];
    t3];;

let BYTE_ZX2_WORD = prove
 (`!x:byte. word_zx (word_zx x:int32):int64 = word (val x)`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [word_zx] THEN REWRITE_TAC[BYTE_ZX1_VAL]);;

(* RIP_DECIDE_TAC with more rewrites ths for the condition first *)
let RIP_DECIDE_EQ_TAC ths bnds =
  let isrip th = let c = concl th in
    is_eq c && can (term_match [] `read RIP s`) (lhs c) && is_cond(rhs c) in
  let isev th = let c = concl th in
    is_eq c && can (term_match [] `read events s`) (lhs c) in
  RULE_ASSUM_TAC(fun th -> if isrip th || isev th then
    REWRITE_RULE (ths @ [BYTE_ZX1_VAL; BYTE_ZX2_VAL])
     (REWRITE_RULE[GLUE_CF_LEMMA; GLUE_ZF_LEMMA] th) else th) THEN
  RIP_DECIDE_TAC bnds;;

let HINTS_EQS_TAC =
  SUBGOAL_THEN `val((b:num->byte)(80 + i)) = glue_suh_new 80 b i` ASSUME_TAC THENL
   [REWRITE_TAC[glue_suh_new]; ALL_TAC] THEN
  SUBGOAL_THEN `0 < i ==> val((b:num->byte)(79 + i)) = mld_hints_start 80 b i` ASSUME_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[mld_hints_start] THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < i ==> ~(i = 0) /\ 80 + (i - 1) = 79 + i`];
    ALL_TAC] THEN
  SUBGOAL_THEN `i = 0 ==> mld_hints_start 80 (b:num->byte) i = 0` ASSUME_TAC THENL
   [SIMP_TAC[mld_hints_start]; ALL_TAC];;

let RIP_REWRITE_TAC ths =
  let isrip th = let c = concl th in
    is_eq c && (can (term_match [] `read RIP s`) (lhs c) ||
                can (term_match [] `read events s`) (lhs c)) in
  RULE_ASSUM_TAC(fun th -> if isrip th then REWRITE_RULE ths th else th);;

let HZ_RIP0_TAC =
  RIP_DECIDE_EQ_TAC [VAL_WORD_ZX_GEN; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64;
                     GLUE_VAL_BYTE_MOD; VAL_WORD; MOD_LT;
                     NUM_REDUCE_CONV `2 EXP 32`; NUM_REDUCE_CONV `2 EXP 64`;
                     NUM_REDUCE_CONV `2 EXP 8`] [];;

let ZX3_BYTE32 = WORD_BLAST `word_zx (word_zx (word_zx (x:byte):int32):int64):int32 = word_zx x`;;

let CF32_BYTE = prove
 (`!(x:byte) n. n < 256
       ==> ((&(val x) - &n:int = &(val(word_sub (word_zx x:int32) (word n)))) <=> n <= val x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`word_zx (x:byte):int32`; `word n:int32`] GLUE_CF_LEMMA) THEN
  REWRITE_TAC[BYTE_ZX1_VAL; VAL_WORD; DIMINDEX_32] THEN
  SUBGOAL_THEN `n MOD 2 EXP 32 = n` (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let ZF32_BYTE = prove
 (`!(x:byte) n. n < 256
       ==> (val(word_sub (word_zx x:int32) (word n)) = 0 <=> val x = n)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GLUE_ZF_LEMMA; BYTE_ZX1_VAL; VAL_WORD; DIMINDEX_32] THEN
  SUBGOAL_THEN `n MOD 2 EXP 32 = n` (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let HZ_RIP_TAC =
  let isrip th = let c = concl th in
    is_eq c && (can (term_match [] `read RIP s`) (lhs c) ||
                can (term_match [] `read events s`) (lhs c)) in
  RULE_ASSUM_TAC(fun th -> if isrip th then
    SIMP_RULE[CF32_BYTE; ZF32_BYTE; ARITH_RULE `80 < 256`]
      (REWRITE_RULE[BYTE_ZX1_VAL]
        (REWRITE_RULE[GLUE_CF_LEMMA; GLUE_ZF_LEMMA] (REWRITE_RULE[ZX3_BYTE32] th))) else th) THEN
  HZ_RIP0_TAC;;

(* the memset of the coefficients at step n - 1 (the call), with the zero
   coefficients as 32-bit words after it *)
let HZ_MEMSET_TAC execth allowed n =
  LIBC_PLT_TAC execth (layout "plt_memset") (layout "got_memset") n THEN
  LIBC_FULL_CALL_TAC "H_MEMSET" execth
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
    `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   allowed (n + 2) THEN
  RSP_NORM_TAC THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && can (find_term ((=) `1024`)) (concl th) &&
       can (find_term ((=) `word_zx:int64->byte`)) (concl th)
    then ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
           (MATCH_MP HZ_ZERO32 (REWRITE_RULE[WORD_ZX_0] th)))
    else NO_TAC);;

let HZ_S1A_TAC execth =
  let allowed = ref [`rsp0:int64`; `sig:int64`; `pc:num`; `b:num->byte`; `i:num`; `mf:int64`] in
  let fin =
    RULE_ASSUM_TAC(REWRITE_RULE[BYTE_ZX2_WORD]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[BYTE_ZX2_WORD] THEN
    REWRITE_TAC[WORD_VAL_ADD_64; GSYM ADD_ASSOC] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    REPEAT CONJ_TAC THEN
    TRY(DISCH_TAC THEN ASM_SIMP_TAC[] THEN NO_TAC) THEN
    PATH_DISCHARGE_TAC in
  let memset_path n =
    X86_STEPS_TAC execth ((n+1)--(n+2)) THEN HZ_RIP_TAC THEN
    X86_STEPS_TAC execth ((n+3)--(n+6)) THEN HZ_MEMSET_TAC execth allowed (n+6) in
  FULL_INIT_TAC THEN HINTS_EQS_TAC THEN
  SUBGOAL_THEN `nonoverlapping (word_add rsp0 (word 1248):int64,1024) (word_sub rsp0 (word 8),8)`
   ASSUME_TAC THENL
   [REWRITE_TAC[WORD_RULE `word_sub (x:int64) y = word_add x (word_neg y)`] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[nonoverlapping; DIMINDEX_64] THEN
    MATCH_MP_TAC(REWRITE_RULE[DIMINDEX_64] (INST_TYPE [`:64`,`:N`] NONOVERLAPPING_MODULO_OFFSET_BOTH)) THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MAP_EVERY (fun t ->
    FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `2336`)) (concl th)
       then MP_TAC(SPEC t th) else NO_TAC) THEN
    ANTS_TAC THENL [LOCAL_ARITH_TAC; DISCH_TAC]) [`80 + i`; `79 + i`] THEN
  VAL_INT64_TAC `i:num` THEN
  ALIAS_ASSUME_TAC ["word_add sig (word (1 * i + 2416)):int64 = word_add sig (word (2336 + 80 + i))";
                    "word_add sig (word (1 * i + 2415)):int64 = word_add sig (word (2336 + 79 + i))"] THEN
  X86_STEPS_TAC execth (1--6) THEN
  ASM_CASES_TAC `0 < i` THEN RIP_DECIDE_TAC [] THEN
  TRY(FIRST_ASSUM(fun th0 -> if concl th0 = `0 < i` then
        FIRST_ASSUM(fun th -> if is_imp(concl th) && lhand(concl th) = `0 < i`
          then ASSUME_TAC(MP th th0) else NO_TAC) else NO_TAC)) THEN
  (ASM_CASES_TAC `80 < glue_suh_new 80 (b:num->byte) i` THENL
   [(* fail: w > 80 *)
    SUBGOAL_THEN `glue_suh_early 80 (b:num->byte) i` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[glue_suh_early]; ALL_TAC] THEN
    X86_STEPS_TAC execth (7--10) THEN HZ_RIP_TAC THEN
    (fun g -> if exists (fun (_,th) -> concl th = `0 < i`) (fst g)
              then X86_STEPS_TAC execth (11--11) g else ALL_TAC g) THEN
    fin;
    X86_STEPS_TAC execth (7--10) THEN HZ_RIP_TAC THEN
    (fun g -> if exists (fun (_,th) -> concl th = `0 < i`) (fst g)
     then
       (ASM_CASES_TAC `glue_suh_new 80 (b:num->byte) i < mld_hints_start 80 b i` THENL
         [SUBGOAL_THEN `glue_suh_early 80 (b:num->byte) i` ASSUME_TAC THENL
           [ASM_REWRITE_TAC[glue_suh_early]; ALL_TAC] THEN
          X86_STEPS_TAC execth (11--12) THEN HZ_RIP_TAC THEN fin;
          SUBGOAL_THEN `~glue_suh_early 80 (b:num->byte) i` ASSUME_TAC THENL
           [ASM_REWRITE_TAC[glue_suh_early]; ALL_TAC] THEN
          memset_path 10 THEN fin]) g
     else
       (SUBGOAL_THEN `mld_hints_start 80 (b:num->byte) i = 0` ASSUME_TAC THENL
         [FIRST_ASSUM(fun th -> if is_imp(concl th) && lhand(concl th) = `i = 0`
                                then MATCH_MP_TAC th else NO_TAC) THEN
          LOCAL_ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `~glue_suh_early 80 (b:num->byte) i` ASSUME_TAC THENL
         [ASM_REWRITE_TAC[glue_suh_early] THEN LOCAL_ARITH_TAC; ALL_TAC] THEN
        memset_path 10 THEN fin) g)]);;


(* ------------------------------------------------------------------------- *)
(* Segment 1b: after the memset, the first hint and the loop over the rest   *)
(* (the region lemma L1), to join7, or to join1 if the hints do not grow.    *)
(* ------------------------------------------------------------------------- *)

let VAL_ZX32_SMALL = prove
 (`!n. n < 256 ==> val(word_zx (word n:int64):int32) = n`,
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  REPEAT STRIP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `n < 256 ==> n < 18446744073709551616`;
               ARITH_RULE `n < 256 ==> n < 4294967296`]);;

let WORD_ZX2_SMALL = prove
 (`!n. n < 256 ==> word_zx (word_zx (word n:int64):int32):int64 = word n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `n < 256 ==> n < 18446744073709551616`;
               ARITH_RULE `n < 256 ==> n < 4294967296`]);;

let INC32_VAL = prove
 (`!n. n < 256
       ==> val(word_zx (word_zx (word_add (word_zx (word n:int64):int32) (word 1)):int64):int32) = n + 1`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `n < 256 ==> n < 18446744073709551616`;
               ARITH_RULE `n < 256 ==> n < 4294967296`;
               ARITH_RULE `n < 256 ==> n + 1 < 18446744073709551616`;
               ARITH_RULE `n < 256 ==> n + 1 < 4294967296`]);;

let HZ_ZX_TAC =
  MAP_EVERY (fun t -> ASSUME_TAC(MATCH_MP VAL_ZX32_SMALL (ASSUME t)))
    [`mld_hints_start 80 (b:num->byte) i < 256`; `glue_suh_new 80 (b:num->byte) i < 256`];;

(* the branch on a comparison of the 32-bit parts of words of small numbers *)
let HZ_B_RIP_TAC =
  W(fun (asl,w) ->
    let zths = filter (fun th ->
        can (term_match [] `val(word_zx (word n:int64):int32) = n`) (concl th) ||
        can (term_match []
          `val(word_zx (word_zx (word_add (word_zx (word n:int64):int32) (word 1)):int64):int32) = n + 1`)
          (concl th))
      (map snd asl) in
    RIP_REWRITE_TAC [GLUE_CF_LEMMA; GLUE_ZF_LEMMA] THEN RIP_REWRITE_TAC zths) THEN
  RIP_DECIDE_TAC [];;

(* the coefficients after the store of the first hint, in state st *)
let HZ_H1_TAC st =
  let sv = mk_var(st,`:x86state`) in
  let gl = subst [sv,`s:x86state`]
    `!q. q < 256 ==> read(memory :> bytes32(word_add rsp0 (word(1248 + 4 * q)))) s =
                     glue_suh_h 80 (b:num->byte) i 1 q` in
  SUBGOAL_THEN gl ASSUME_TAC THENL
   [X_GEN_TAC `q:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`80`; `b:num->byte`; `i:num`; `0`; `q:num`] GLUE_SUH_H_ADD1) THEN
    REWRITE_TAC[ADD_CLAUSES; GLUE_SUH_H_0] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(ACCEPT_TAC o GSYM)];
    ALL_TAC];;

(* A segment of no steps, when the start is already the end (a failure, at
   join1): the events of the segment are [], the conditions cs are true. *)
let NIL_EVENTS_TAC (asl,w) =
  let l,r = dest_eq w in
  let ap = lhand r in
  let f,args = strip_comb ap in
  let lam = list_mk_abs(args, mk_mconst("NIL", type_of l)) in
  let tm = mk_eq(l, mk_comb(mk_comb(rator(rator r), list_mk_comb(lam,args)), l)) in
  let th = prove(tm, CONV_TAC(RAND_CONV(LAND_CONV(TOP_DEPTH_CONV BETA_CONV))) THEN
                     REWRITE_TAC[APPEND]) in
  UNIFY_ACCEPT_TAC [f] th (asl,w);;

let HZ_SKIP_TAC (cs:term list) =
  MATCH_MP_TAC ENSURES_ALREADY THEN CONJ_TAC THENL
   [REWRITE_TAC(map ASSUME cs) THEN X_GEN_TAC `s:x86state` THEN
    W(fun _ ->
      let v = genvar `:(uarch_event)list` in
      DISCH_THEN(fun th ->
        let cths = CONJUNCTS th in
        let evth = find (fun c -> is_exists(concl c)) cths in
        MAP_EVERY ASSUME_TAC (filter (fun c -> c != evth) cths) THEN
        X_CHOOSE_THEN v (fun eth -> MAP_EVERY ASSUME_TAC (CONJUNCTS eth)) evth) THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
      TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
      EXISTS_TAC v THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
      FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = v
                            then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
      NIL_EVENTS_TAC);
    SUBSUMED_ID_MAYCHANGE_TAC];;

(* PATH_DISCHARGE_TAC for a segment after the first, whose precondition has
   the events of the segments before, e2 = TMPL with memaccess_inbounds e2:
   the memory-safety goal and that assumption are split over the APPENDs,
   so that each part of the goal is a part of the assumption, the events
   of a region lemma or of a callee, or concrete. The events as found and
   those of the template can differ in the association of the APPENDs. *)
let SEG_DISCHARGE_TAC =
  let beta_all =
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) in
  let select_tac =
    W(fun (asl,w) ->
      let conds = map (fun t -> rand(rator(rator t))) (find_terms is_cond w) in
      let ths = mapfilter (fun (_,th) ->
        let c = concl th in
        if mem c conds then EQT_INTRO th
        else if is_neg c && mem (rand c) conds then EQF_INTRO th
        else failwith "") asl in
      REWRITE_TAC ths) in
  let is_vdef th = let c = concl th in
    is_eq c && is_var(lhs c) && type_of(lhs c) = `:(uarch_event)list` in
  let is_meminb v th = let c = concl th in
    (match strip_comb c with
       Const("memaccess_inbounds",_),(e::_) -> e = v
     | _ -> false) in
  let split_tac =
    W(fun (asl,w) ->
      let defs = filter is_vdef (map snd asl) in
      MAP_EVERY (fun dth ->
        let v = lhs(concl dth) in
        MAP_EVERY (fun (_,mth) ->
          if is_meminb v mth then
            STRIP_ASSUME_TAC(REWRITE_RULE[MEMACCESS_INBOUNDS_APPEND] (REWRITE_RULE[dth] mth))
          else ALL_TAC) asl) defs) in
  REWRITE_TAC[ENUMERATEL_ADD1] THEN beta_all THEN select_tac THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W(fun (asl,w) ->
    if is_conj w then
      CONJ_TAC THENL
       [(REWRITE_TAC[APPEND_ASSOC] THEN NO_TAC) ORELSE FULL_UNIFY_F_EVENTS_TAC;
        ALL_TAC]
    else ALL_TAC) THEN
  beta_all THEN
  REWRITE_TAC[NOT_LT] THEN RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
  split_tac THEN
  REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN REPEAT CONJ_TAC THEN
  DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

(* the frame: a store at a byte-indexed address in it needs the bound of the
   byte, as in the region lemmas *)
let HZ_MAYCHANGE_TAC =
  FIRST_X_ASSUM(fun th -> if maychange_term (concl th) && not(is_forall(concl th))
                          then MP_TAC th else NO_TAC) THEN
  VAL_BYTE_GEN_TAC THEN DISCH_TAC THEN MONOTONE_MAYCHANGE_TAC;;

let HZ_FIN_B_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(X_GEN_TAC `q:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN NO_TAC) THEN
  TRY(HZ_MAYCHANGE_TAC THEN NO_TAC) THEN
  BYTE_IDX_DISCHARGE_TAC SEG_DISCHARGE_TAC;;

let HZ_OK1_SMALL = prove
 (`!(b:num->byte) i. ~(mld_hints_start 80 b i + 1 < glue_suh_new 80 b i)
                     ==> glue_suh_ok1 80 b i`,
  REWRITE_TAC[glue_suh_ok1] THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;

let HZ_S1B_TAC execth =
  let s_ = `mld_hints_start 80 (b:num->byte) i` in
  let bs_ = `(b:num->byte)(mld_hints_start 80 b i)` in
  let allowed = [`rsp0:int64`; `sig:int64`; `pc:num`; `b:num->byte`; `i:num`; `mf:int64`] in
  let zx2 = `word_zx (word_zx (word (mld_hints_start 80 (b:num->byte) i):int64):int32):int64 =
             word (mld_hints_start 80 b i)` in
  let ok1_tac =
    SUBGOAL_THEN `glue_suh_ok1 80 (b:num->byte) i` ASSUME_TAC THENL
     [MATCH_MP_TAC HZ_OK1_SMALL THEN LOCAL_ARITH_TAC; ALL_TAC] in
  ASM_CASES_TAC `glue_suh_early 80 (b:num->byte) i` THENL
   [HZ_SKIP_TAC [`glue_suh_early 80 (b:num->byte) i`];
    REWRITE_TAC[ASSUME `~glue_suh_early 80 (b:num->byte) i`] THEN
    MP_TAC(REWRITE_RULE[glue_suh_early; DE_MORGAN_THM]
            (ASSUME `~glue_suh_early 80 (b:num->byte) i`)) THEN STRIP_TAC THEN
    ASM_CASES_TAC `mld_hints_start 80 (b:num->byte) i < glue_suh_new 80 b i` THENL
     [FULL_INIT_TAC THEN
      ASSUME_TAC(MATCH_MP WORD_ZX2_SMALL (ASSUME `mld_hints_start 80 (b:num->byte) i < 256`)) THEN
      FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `2336`)) (concl th)
          then MP_TAC(SPEC s_ th) else NO_TAC) THEN
      ANTS_TAC THENL [LOCAL_ARITH_TAC; DISCH_TAC] THEN
      VAL_INT64_TAC s_ THEN
      ALIAS_ASSUME_TAC ["word_add sig (word (1 * mld_hints_start 80 b i + 2336)):int64 = word_add sig (word (2336 + mld_hints_start 80 b i))"] THEN
      X86_STEPS_TAC execth (1--5) THEN HZ_ZX_TAC THEN HZ_B_RIP_TAC THEN
      X86_STEPS_TAC execth (6--6) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ASSUME zx2]) THEN
      X86_STEPS_TAC execth (7--7) THEN
      FIRST_ASSUM(fun th ->
        if is_forall(concl th) && can (find_term ((=) `1248`)) (concl th) &&
           not(is_imp(snd(dest_forall(concl th))) && is_conj(lhand(snd(dest_forall(concl th))))) then
          ASSUME_TAC(TAC_PROOF(([],
            `!q. q < 256 /\ ~(q = val((b:num->byte)(mld_hints_start 80 b i)))
                 ==> read(memory :> bytes32(word_add rsp0 (word(1248 + 4 * q)))) s7 = word 0`),
            REPEAT STRIP_TAC THEN MATCH_MP_TAC th THEN ASM_REWRITE_TAC[]))
        else NO_TAC) THEN
      ASSUME_TAC(SPEC bs_ GLUE_VAL_BYTE) THEN
      ASSUME_TAC(ISPEC bs_ BYTE_ZX2_VAL) THEN
      ALIAS_ASSUME_TAC ["word_add rsp0 (word (4 * val ((b:num->byte) (mld_hints_start 80 b i)) + 1248)):int64 = word_add rsp0 (word (1248 + 4 * val ((b:num->byte) (mld_hints_start 80 b i))))"] THEN
      X86_STEPS_TAC execth (8--11) THEN HZ_H1_TAC "s11" THEN
      ASSUME_TAC(MATCH_MP INC32_VAL (ASSUME `mld_hints_start 80 (b:num->byte) i < 256`)) THEN
      ASM_CASES_TAC `mld_hints_start 80 (b:num->byte) i + 1 < glue_suh_new 80 b i` THEN
      HZ_B_RIP_TAC THENL
       [FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc execth "H_L1"
         [`sig:int64`; `rsp0:int64`; `pc:num`; `b:num->byte`; `i:num`] allowed 12 THEN
        ASM_CASES_TAC `glue_suh_ok1 80 (b:num->byte) i` THENL
         [FIRST_X_ASSUM(fun th -> if is_imp(concl th) &&
                                     lhand(concl th) = `glue_suh_ok1 80 (b:num->byte) i`
             then ASSUME_TAC(MP th (ASSUME `glue_suh_ok1 80 (b:num->byte) i`)) else NO_TAC) THEN
          HZ_FIN_B_TAC;
          HZ_FIN_B_TAC];
        ok1_tac THEN
        SUBGOAL_THEN `!q. mld_unpack_hints 80 (b:num->byte) i q = glue_suh_h 80 b i 1 q`
         ASSUME_TAC THENL
         [GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC GLUE_SUH_H_FULL THEN LOCAL_ARITH_TAC;
          ALL_TAC] THEN
        HZ_FIN_B_TAC];
      FULL_INIT_TAC THEN
      X86_STEPS_TAC execth (1--5) THEN HZ_ZX_TAC THEN HZ_B_RIP_TAC THEN
      ok1_tac THEN
      SUBGOAL_THEN `!q. mld_unpack_hints 80 (b:num->byte) i q = word 0` ASSUME_TAC THENL
       [GEN_TAC THEN
        MP_TAC(SPECL [`80`; `b:num->byte`; `i:num`; `0`; `q:num`] GLUE_SUH_H_FULL) THEN
        REWRITE_TAC[GLUE_SUH_H_0; ADD_CLAUSES] THEN
        ANTS_TAC THENL [LOCAL_ARITH_TAC; SIMP_TAC[]];
        ALL_TAC] THEN
      HZ_FIN_B_TAC]];;

(* ------------------------------------------------------------------------- *)
(* Segment 2: from join7, the check of the unused hint bytes after the last  *)
(* polynomial (the region lemma L2, for i = 3 and w < 80), to join8, or to   *)
(* join1 if one of them is not zero.                                         *)
(* ------------------------------------------------------------------------- *)

let VAL_ZX8_SMALL = prove
 (`!n. n < 256 ==> val(word_zx (word n:int64):byte) = n`,
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_64] THEN
  REPEAT STRIP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `n < 256 ==> n < 18446744073709551616`]);;

let HZ_CL_ZEROS_80 = prove
 (`!(b:num->byte) w. ~(w < 80) ==> cl_zeros 80 b w`,
  REWRITE_TAC[cl_zeros] THEN ARITH_TAC);;

let CF8_NUM = prove
 (`!(x:byte) n. n < 256
       ==> ((&(val x) - &n:int = &(val(word_sub x (word n)))) <=> n <= val x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`x:byte`; `word n:byte`] GLUE_CF_LEMMA) THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  SUBGOAL_THEN `n MOD 2 EXP 8 = n` (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let HZ_S2_TAC execth =
  let c = `glue_suh_early 80 (b:num->byte) i \/ ~glue_suh_ok1 80 b i` in
  let ok = `mld_unpack_hints_ok 80 4 (b:num->byte) i` in
  let w_ = `glue_suh_new 80 (b:num->byte) i` in
  let allowed = [`rsp0:int64`; `sig:int64`; `pc:num`; `b:num->byte`; `i:num`; `mf:int64`] in
  let fin =
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(X_GEN_TAC `q:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN NO_TAC) in
  let i3 =
    SUBGOAL_THEN `i = 3` ASSUME_TAC THENL [LOCAL_ARITH_TAC; ALL_TAC] in
  ASM_CASES_TAC c THENL
   [SUBGOAL_THEN (mk_neg ok) ASSUME_TAC THENL
     [UNDISCH_TAC c THEN REWRITE_TAC[GLUE_SUH_OK] THEN CONV_TAC TAUT; ALL_TAC] THEN
    HZ_SKIP_TAC [c; mk_neg ok];
    REWRITE_TAC[ASSUME (mk_neg c)] THEN
    MP_TAC(REWRITE_RULE[DE_MORGAN_THM] (ASSUME (mk_neg c))) THEN STRIP_TAC THEN
    ASM_CASES_TAC `i < 3` THENL
     [SUBGOAL_THEN `~(i = 3)` ASSUME_TAC THENL [LOCAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN ok ASSUME_TAC THENL
       [REWRITE_TAC[GLUE_SUH_OK] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      FULL_INIT_TAC THEN X86_STEPS_TAC execth (1--3) THEN RIP_DECIDE_TAC [`i:num`; `3`] THEN
      fin THEN SEG_DISCHARGE_TAC;
      SUBGOAL_THEN (mk_iff(ok, `cl_zeros 80 (b:num->byte) (glue_suh_new 80 b i)`)) ASSUME_TAC THENL
       [REWRITE_TAC[GLUE_SUH_OK] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
        SUBGOAL_THEN `i = 3` (fun th -> REWRITE_TAC[EQT_INTRO th]) THENL
         [LOCAL_ARITH_TAC; REWRITE_TAC[glue_suh_zeros; cl_zeros]];
        ALL_TAC] THEN
      FIRST_ASSUM(fun th -> if is_iff(concl th) && lhand(concl th) = ok
                            then REWRITE_TAC[th] else NO_TAC) THEN
      FULL_INIT_TAC THEN
      ASSUME_TAC(MATCH_MP VAL_ZX8_SMALL (ASSUME `glue_suh_new 80 (b:num->byte) i < 256`)) THEN
      ASSUME_TAC(MATCH_MP WORD_ZX2_SMALL (ASSUME `glue_suh_new 80 (b:num->byte) i < 256`)) THEN
      X86_STEPS_TAC execth (1--3) THEN RIP_DECIDE_TAC [`i:num`; `3`] THEN
      X86_STEPS_TAC execth (4--5) THEN
      W(fun (asl,w) ->
        let zths = filter (fun th ->
            can (term_match [] `val(word_zx (word n:int64):byte) = n`) (concl th)) (map snd asl) in
        RIP_REWRITE_TAC [WORD_VAL_MOD_256] THEN
        RULE_ASSUM_TAC(fun th ->
          if is_eq(concl th) && can (term_match [] `read RIP s`) (lhs(concl th))
          then SIMP_RULE[CF8_NUM; ARITH_RULE `80 < 256`] th else th) THEN
        RIP_REWRITE_TAC zths) THEN
      ASM_CASES_TAC `glue_suh_new 80 (b:num->byte) i < 80` THEN
      RIP_DECIDE_TAC [] THENL
       [X86_STEPS_TAC execth (6--7) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WORD_ZX2_SMALL
          (ASSUME `glue_suh_new 80 (b:num->byte) i < 256`)]) THEN
        FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc execth "H_L2"
         [`sig:int64`; w_; `pc:num`; `b:num->byte`] allowed 8 THEN
        ASM_CASES_TAC `cl_zeros 80 (b:num->byte) (glue_suh_new 80 b i)` THEN
        fin THEN i3 THEN SEG_DISCHARGE_TAC;
        SUBGOAL_THEN `cl_zeros 80 (b:num->byte) (glue_suh_new 80 b i)` ASSUME_TAC THENL
         [MATCH_MP_TAC HZ_CL_ZEROS_80 THEN LOCAL_ARITH_TAC; ALL_TAC] THEN
        fin THEN i3 THEN SEG_DISCHARGE_TAC]]];;

(* ------------------------------------------------------------------------- *)
(* Segment 3: from join8 to the use of the hints at join11.                  *)
(* ------------------------------------------------------------------------- *)

let HZ_S3_TAC execth =
  let ok = `mld_unpack_hints_ok 80 4 (b:num->byte) i` in
  ASM_CASES_TAC ok THENL
   [REWRITE_TAC[ASSUME ok] THEN FULL_INIT_TAC THEN X86_STEPS_TAC execth (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(X_GEN_TAC `q:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN NO_TAC) THEN
    SEG_DISCHARGE_TAC;
    HZ_SKIP_TAC [mk_neg ok]];;

(* ------------------------------------------------------------------------- *)
(* The whole region.                                                         *)
(* ------------------------------------------------------------------------- *)

let PROVE_HINTS44 fn =
  let mc = mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc in
  let ex1a = X86_MK_EXEC_RANGES_RULE mc
    [(layout (fn^"_loop9_exit"), layout (fn^"_after_memset_7") + 0x13);
     layout_range "plt_memset"]
  and ex1b = X86_MK_EXEC_RANGES_RULE mc
    [(layout (fn^"_after_memset_7"), layout (fn^"_join7"))]
  and ex2 = X86_MK_EXEC_RANGES_RULE mc
    [(layout (fn^"_join7"), layout (fn^"_loop10"))]
  and ex3 = X86_MK_EXEC_RANGES_RULE mc
    [(layout (fn^"_join8"), layout (fn^"_join8") + 0x14)] in
  let l1th = PROVE_L1 fn and l2th = PROVE_L2 fn in
  prove(HINTS44_STMT fn,
        HINTS_SETUP_TAC fn l1th l2th (HZ_S1A_TAC ex1a) (HZ_S1B_TAC ex1b)
          (HZ_S2_TAC ex2) (HZ_S3_TAC ex3));;
