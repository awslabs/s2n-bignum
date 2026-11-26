(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The loops of poly_invntt_tomont of the clang 23 build that are not        *)
(* vectorised: layers 8 to 4 (a block of 2 to 32 coefficients per            *)
(* iteration, with an index register that starts below 0 and a pointer to    *)
(* the zetas that goes down by 4 per block), as the lemma for the first      *)
(* iteration (head to head) and the lemma for the other iterations, and the  *)
(* loop that scales each coefficient by mld_fqscale. The vectorised loops    *)
(* of layers 3 to 1 come from the generator of ntt_loops.ml, with            *)
(* ntt_inverse set.                                                          *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/ntt_tools.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/ntt_loops.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_invntt_tomont_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The blocks of a layer of the inverse NTT. *)
(* ------------------------------------------------------------------------- *)

(* the blocks of a layer of the inverse NTT: what block b changes *)
let INTT_BLOCKS_UNCH = prove
 (`!m r b j. 2 * 2 EXP (8 - m) * b <= j ==> mld_invntt_blocks m b r j = r j`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[mld_invntt_blocks];
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[mld_invntt_blocks; mld_invntt_block] THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let INTT_BLOCKS_PREV = prove
 (`!m r b j. j < 2 * 2 EXP (8 - m) * b ==> mld_invntt_blocks m (SUC b) r j = mld_invntt_blocks m b r j`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[mld_invntt_blocks; mld_invntt_block] THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[]);;

let INTT_BLOCKS_LO = prove
 (`!m r b k. k < 2 EXP (8 - m)
     ==> mld_invntt_blocks m (SUC b) r (2 * 2 EXP (8 - m) * b + k) =
         word_add (r (2 * 2 EXP (8 - m) * b + k)) (r ((2 * 2 EXP (8 - m) * b + k) + 2 EXP (8 - m)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[mld_invntt_blocks; mld_invntt_block] THEN
  COND_CASES_TAC THENL
   [MP_TAC(SPECL [`m:num`; `r:num->int32`; `b:num`; `2 * 2 EXP (8 - m) * b + k`] INTT_BLOCKS_UNCH) THEN
    ANTS_TAC THENL [ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`m:num`; `r:num->int32`; `b:num`; `(2 * 2 EXP (8 - m) * b + k) + 2 EXP (8 - m)`] INTT_BLOCKS_UNCH) THEN
    ANTS_TAC THENL [ARITH_TAC; DISCH_TAC] THEN
    ASM_REWRITE_TAC[];
    ASM_ARITH_TAC]);;

let INTT_BLOCKS_HI = prove
 (`!m r b k. k < 2 EXP (8 - m)
     ==> mld_invntt_blocks m (SUC b) r ((2 * 2 EXP (8 - m) * b + 2 EXP (8 - m)) + k) =
         mld_fqmul (word_sub (r (2 * 2 EXP (8 - m) * b + k)) (r ((2 * 2 EXP (8 - m) * b + 2 EXP (8 - m)) + k)))
                   (word_neg (mld_zeta (2 EXP m - 1 - b)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[mld_invntt_blocks; mld_invntt_block] THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [MP_TAC(SPECL [`m:num`; `r:num->int32`; `b:num`; `2 * 2 EXP (8 - m) * b + k`] INTT_BLOCKS_UNCH) THEN
    ANTS_TAC THENL [ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`m:num`; `r:num->int32`; `b:num`; `(2 * 2 EXP (8 - m) * b + 2 EXP (8 - m)) + k`] INTT_BLOCKS_UNCH) THEN
    ANTS_TAC THENL [ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `((2 * 2 EXP (8 - m) * b + 2 EXP (8 - m)) + k) - 2 EXP (8 - m) = 2 * 2 EXP (8 - m) * b + k` SUBST1_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The first iteration of a scalar loop. *)
(* ------------------------------------------------------------------------- *)

let ihas_blocks tm = can (find_term (fun t -> is_const t && fst(dest_const t) = "mld_invntt_blocks")) tm;;
(* ------------------------------------------------------------------------- *)
(* The scalar loops of the inverse NTT (layers m = 8 to 5): a block of n     *)
(* coefficients per iteration, an index register that starts at -c (so that  *)
(* the first iteration is proved on its own) and a pointer to the zetas that *)
(* goes down by 4 for each block.                                            *)
(* ------------------------------------------------------------------------- *)

type iloop = { ih : int; ie : int; im : int; inn : int; ic : int; inb : int };;

let neg64 c = string_of_num (sub_num (power_num (num 2) (num 64)) (num c));;

let iz_reg = par_local_ref (fun () -> "RCX");;
let ii_reg = par_local_ref (fun () -> "RDX");;
let ib_off = par_local_ref (fun () -> 0);;

let ibix = function Some k -> string_of_int k | None -> "(i + 1)";;

let iscal_regs lp bi =
  let mi = (1 lsl lp.im) - 1 in
  let zp = match bi with
      Some 0 -> Printf.sprintf "word_add zt (word %d)" (4 * mi)
    | Some k -> Printf.sprintf "word_add zt (word %d)" (4 * (mi - k))
    | None -> Printf.sprintf "word_sub (word_add zt (word %d)) (word (4 * (i + 1)))" (4 * mi) in
  let rd = match bi with
      Some 0 -> neg64 lp.ic
    | Some k -> string_of_int (lp.ic * (k - 1))
    | None -> Printf.sprintf "%d * i" lp.ic in
  Printf.sprintf
   "read RDI s = a /\\ read RAX s = word 0x0380200100000000 /\\ %sread %s s = %s /\\
    read %s s = word (%s) /\\
    (!k. k < 256 ==> read (memory :> bytes32 (word_add zt (word (4 * k)))) s = mld_zeta k)"
   (if !(ib_off ()) > 0 then Printf.sprintf "read RCX s = word_add a (word %d) /\\ " !(ib_off ()) else "") !(iz_reg ()) zp !(ii_reg ()) rd;;

let iscal_inv lp bi =
  let ii = ibix bi in
  Printf.sprintf
   "(!j. j < %d * %s ==> %s = mld_invntt_blocks %d %s x j) /\\
    (!j. %d * %s <= j /\\ j < 256 ==> %s = x j)"
   lp.inn ii (scal_mem_s "s" "j") lp.im ii lp.inn ii (scal_mem_s "s" "j");;

let iscal_all lp bi =
  Printf.sprintf "%s /\\ (!j. j < 256 ==> %s = mld_invntt_blocks %d %s x j)"
    (iscal_regs lp bi) (scal_mem_s "s" "j") lp.im (ibix bi);;

let iscal_flags = "MAYCHANGE [RIP; RCX; RDX; RSI; R8; R9; R10; R11; RBX] ,, MAYCHANGE SOME_FLAGS ,,\n      MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,1024)]";;

let iscal_pre =
 "aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    nonoverlapping (a,1024) (word pc,libmldsa_size) /\\
    nonoverlapping (a,1024) (zt,1024)";;

(* the first iteration, from the head to the head *)
let iscal_first_stmt lp =
  Printf.sprintf
"exists f_events. forall e a pc zt (x:num->int32).
    %s
    ==> ensures x86
     (\\s. bytes_loaded s (word pc) %s /\\
          read RIP s = word (pc + %d) /\\
          %s /\\
          (!j. j < 256 ==> %s = x j) /\\
          read events s = e)
     (\\s. read RIP s = word (pc + %d) /\\
          %s /\\
          (exists e2. read events s = APPEND e2 e /\\ e2 = f_events a pc zt /\\
              memaccess_inbounds e2 [a,1024; zt,1024] [a,1024]))
     (%s)"
   iscal_pre ntt_mc (!(ntt_fn_base ()) + lp.ih) (iscal_regs lp (Some 0)) (scal_mem_s "s" "j")
   (!(ntt_fn_base ()) + lp.ih) (iscal_all lp (Some 1)) iscal_flags;;

(* the loop for the blocks 1 to nb - 1 *)
let iscal_stmt lp =
  Printf.sprintf
"exists f_events. forall e a pc zt (x:num->int32).
    %s
    ==> ensures x86
     (\\s. bytes_loaded s (word pc) %s /\\
          read RIP s = word (pc + %d) /\\
          %s /\\
          read events s = e)
     (\\s. read RIP s = word (pc + %d) /\\
          %s /\\
          (exists e2. read events s = APPEND e2 e /\\ e2 = f_events a pc zt /\\
              memaccess_inbounds e2 [a,1024; zt,1024] [a,1024]))
     (%s)"
   iscal_pre ntt_mc (!(ntt_fn_base ()) + lp.ih) (iscal_all lp (Some 1))
   (!(ntt_fn_base ()) + lp.ie) (iscal_all lp (Some lp.inb)) iscal_flags;;

let SPLIT_LO = prove
 (`!n. n <= 256
     ==> !(P:num->bool). ((!j. j < 256 ==> P j) <=> (!j. j < n ==> P j) /\ (!j. n <= j /\ j < 256 ==> P j))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    STRIP_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `j < n` THENL [ASM_SIMP_TAC[]; ASM_MESON_TAC[NOT_LT]]]);;

(* the instances of the lemmas on the blocks of layer m, for the block b *)
let iblk_insts m (bt:term) =
  let mt = mk_small_numeral m in
  let len = 1 lsl (8 - m) in
  let red th = CONV_RULE (DEPTH_CONV NUM_RED_CONV) th in
  let nrm th = CONV_RULE NORM_R_CONV (red th) in
  let inst lem k = nrm (SPECL [mt; `x:num->int32`; bt; mk_small_numeral k] lem) in
  let prev = nrm (SPECL [mt; `x:num->int32`; bt; `j:num`] INTT_BLOCKS_PREV) in
  let unch = nrm (SPECL [mt; `x:num->int32`; bt; `j:num`] INTT_BLOCKS_UNCH) in
  (prev, unch, map (inst INTT_BLOCKS_LO) (0--(len-1)), map (inst INTT_BLOCKS_HI) (0--(len-1)));;


let iscal_exec lp = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc [(!(ntt_fn_base ()) + lp.ih, !(ntt_fn_base ()) + lp.ie)];;

(* the facts for the block of the first iteration and its zeta *)
let iscal_first_prep lp =
  let n = lp.inn and mi = (1 lsl lp.im) - 1 in
  let pat = parse_term(Printf.sprintf "!j. j < 256 ==> %s = (x:num->int32) j" (scal_mem_s "s0" "j")) in
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [MATCH_MP (SPEC (mk_small_numeral n) SPLIT_LO) (EQT_ELIM(NUM_REDUCE_CONV (parse_term(Printf.sprintf "%d <= 256" n))))] o
     check (fun th -> aconv (concl th) pat)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  EVERY(map (fun k ->
    let addr = if k = 0 then "a" else Printf.sprintf "word_add a (word %d)" (4 * k) in
    let tm = parse_term(Printf.sprintf "read (memory :> bytes32 (%s)) s0 = (x:num->int32) %d" addr k) in
    SUBGOAL_THEN tm ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC (mk_small_numeral k) o
        check (fun th -> can (term_match [] (parse_term(Printf.sprintf "!j. j < %d ==> %s = (x:num->int32) j" n (scal_mem_s "s0" "j")))) (concl th))) THEN
      ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN DISCH_THEN ACCEPT_TAC;
      ALL_TAC]) (0--(n-1))) THEN
  SUBGOAL_THEN (parse_term(Printf.sprintf "read (memory :> bytes32 (word_add zt (word %d))) s0 = mld_zeta %d" (4 * mi) mi)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC (mk_small_numeral mi) o
      check (fun th -> can (term_match [] `!k. k < 256 ==> read (memory :> bytes32 (word_add zt (word (4 * k)))) s0 = mld_zeta k`) (concl th))) THEN
    ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN DISCH_THEN ACCEPT_TAC;
    ALL_TAC];;

let INTT_LEA1 = prove(`!x y:int32. (word_sx (word_add (word_zx y:int64) (word (val (word_zx x:int64)))):int32) = word_add x y`,
   REPEAT GEN_TAC THEN REWRITE_TAC[WORD_VAL; WORD_BLAST `word_sx (v:int64):int32 = word_zx v`] THEN
   SIMP_TAC[WORD_ZX_ADD; DIMINDEX_32; DIMINDEX_64; ARITH] THEN REWRITE_TAC[WORD_ZX_ZX_32_64_32; WORD_ADD_SYM]);;
let INTT_LEA2 = prove(`!x y:int32. (word_sx (word_add (word_zx x:int64) (word (val (word_zx y:int64)))):int32) = word_add x y`,
   REPEAT GEN_TAC THEN REWRITE_TAC[WORD_VAL; WORD_BLAST `word_sx (v:int64):int32 = word_zx v`] THEN
   SIMP_TAC[WORD_ZX_ADD; DIMINDEX_32; DIMINDEX_64; ARITH] THEN REWRITE_TAC[WORD_ZX_ZX_32_64_32]);;

let iscal_post_rules = [NTT_MONTRED_CLANG; WORD_ZX_ZX_32_64_32; WORD_SUB_LZERO; GSYM mld_fqmul; INTT_LEA1; INTT_LEA2];;

(* closing the first iteration: registers, the blocks and the events *)
let iscal_first_final lp =
  let n = lp.inn in
  let (_,_,los,his) = iblk_insts lp.im `0` in
  let unch1 = CONV_RULE NORM_R_CONV (CONV_RULE (DEPTH_CONV NUM_RED_CONV)
     (SPECL [mk_small_numeral lp.im; `x:num->int32`; `1`; `j:num`] INTT_BLOCKS_UNCH)) in
  ENSURES_FINAL_STATE_TAC THEN CONV_TAC NORM_R_CONV THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  (fun gl ->
    let w = snd gl in
    if is_exists w then DISCHARGE_SAFETY_PROPERTY_TAC gl
    else if ihas_blocks w then
      (GEN_REWRITE_TAC I [MATCH_MP (SPEC (mk_small_numeral n) SPLIT_LO) (EQT_ELIM(NUM_REDUCE_CONV (parse_term(Printf.sprintf "%d <= 256" n))))] THEN
       CONJ_TAC THENL
        [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NORM_R_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
         REWRITE_TAC(los @ his) THEN ASM_REWRITE_TAC[] THEN TRY(CONV_TAC WORD_RULE);
         X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[unch1]]) gl
    else TRY(CONV_TAC WORD_RULE) gl);;

(* ------------------------------------------------------------------------- *)
(* The other iterations of a scalar loop. *)
(* ------------------------------------------------------------------------- *)

(* the loop for the blocks 1 to nb - 1: i + 1 blocks are done at the head *)
let iscal_loop_inv lp ii =
  Printf.sprintf
   "read RDI s = a /\\ read RAX s = word 0x0380200100000000 /\\ %s
    read %s s = word_add zt (word (4 * (%d - %s))) /\\
    read %s s = word (%d * %s) /\\
    (!k. k < 256 ==> read (memory :> bytes32 (word_add zt (word (4 * k)))) s = mld_zeta k) /\\
    (!j. j < %d * %s ==> %s = mld_invntt_blocks %d %s x j) /\\
    (!j. %d * %s <= j /\\ j < 256 ==> %s = x j)"
   (if !(ib_off ()) > 0 then Printf.sprintf "read RCX s = word_add a (word %d) /\\" !(ib_off ()) else "")
   !(iz_reg ()) ((1 lsl lp.im) - 1) (Printf.sprintf "(%s + 1)" ii) !(ii_reg ()) lp.ic ii
   lp.inn (Printf.sprintf "(%s + 1)" ii) (scal_mem_s "s" "j") lp.im (Printf.sprintf "(%s + 1)" ii)
   lp.inn (Printf.sprintf "(%s + 1)" ii) (scal_mem_s "s" "j");;

let iscal_loop_skel exec lp body_tac =
  let unch1 = CONV_RULE NORM_R_CONV (CONV_RULE (DEPTH_CONV NUM_RED_CONV)
     (SPECL [mk_small_numeral lp.im; `x:num->int32`; `1`; `j:num`] INTT_BLOCKS_UNCH)) in
  let nbl = lp.inb - 1 in
  CONCRETIZE_F_EVENTS_TAC
   (parse_term(Printf.sprintf
     "\\(a:int64) (pc:num) (zt:int64).
        APPEND (f_ev_epil a pc zt)
         (APPEND (ENUMERATEL %d (\\i. f_ev_loop a pc zt i)) (f_ev_prol a pc zt))
      :(uarch_event)list" nbl)) THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `pc:num`; `zt:int64`; `x:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC (mk_small_numeral nbl)
   (parse_term(Printf.sprintf "pc + %d" (!(ntt_fn_base ()) + lp.ih)))
   (parse_term(Printf.sprintf "pc + %d" (!(ntt_fn_base ()) + lp.ie)))
   (parse_term(Printf.sprintf "\\i s. %s" (iscal_loop_inv lp "i"))) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    (*** init ***)
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
    CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> ihas_blocks (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC];
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> ihas_blocks (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN ASM_SIMP_TAC[unch1];
      DISCHARGE_SAFETY_PROPERTY_TAC];
    (*** body ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    body_tac;
    (*** exit ***)
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_RED_CONV)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let iscal_loop_prep lp =
  let n = lp.inn and c = lp.ic and mi = (1 lsl lp.im) - 1 in
  let nl = 256 / n in ignore nl;
  FULL_INIT_TAC THEN
  SUBGOAL_THEN (parse_term(Printf.sprintf "val(word (%d * i):int64) = %d * i" c c)) ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN NUM_ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (parse_term(Printf.sprintf
     "read (memory :> bytes32 (word_add zt (word (4 * (%d - (i + 1)))))) s0 = mld_zeta (%d - (i + 1))" mi mi))
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC (parse_term(Printf.sprintf "%d - (i + 1)" mi)) o
      check (fun th -> can (term_match [] `!k. k < 256 ==> read (memory :> bytes32 (word_add zt (word (4 * k)))) s0 = mld_zeta k`) (concl th))) THEN
    ANTS_TAC THENL [NUM_ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC];
    ALL_TAC];;

let iscal_loop_chunks lp =
  let n = lp.inn in
  let pat = parse_term(Printf.sprintf
    "!j. %d * (i + 1) <= j /\\ j < 256 ==> %s = (x:num->int32) j" n (scal_mem_s "s0" "j")) in
  SUBGOAL_THEN (parse_term(Printf.sprintf "%d * ((i + 1) + 1) <= 256" n)) ASSUME_TAC THENL
   [NUM_ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [MATCH_MP (SPECL [`i + 1`; mk_small_numeral n; `256`] NTT_CHUNK_IN_L)
        (ASSUME (parse_term(Printf.sprintf "%d * ((i + 1) + 1) <= 256" n)))] o
     check (fun th -> aconv (concl th) pat)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  EVERY(map (fun k ->
    let tm = parse_term(Printf.sprintf
      "read (memory :> bytes32 (word_add a (word (%d * i + %d)))) s0 = (x:num->int32) (%d * i + %d)"
      (4 * n) (4 * n + 4 * k) n (n + k)) in
    SUBGOAL_THEN tm ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC (mk_small_numeral k) o
        check (fun th -> can (term_match [] `!k. k < n ==> read (memory :> bytes32 (word_add a (word (4 * (n * (i + 1) + k))))) s0 = x (n * (i + 1) + k)`) (concl th))) THEN
      ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      CONV_TAC NORM_R_CONV THEN DISCH_THEN ACCEPT_TAC;
      ALL_TAC] THEN
    (let tm2 = parse_term(Printf.sprintf
      "read (memory :> bytes32 (word_add a (word (4 * (%d * i) + %d)))) s0 = (x:num->int32) (%d * i + %d)"
      lp.ic (4 * n + 4 * k) n (n + k)) in
     SUBGOAL_THEN tm2 ASSUME_TAC THENL
      [SUBGOAL_THEN (parse_term(Printf.sprintf "4 * (%d * i) + %d = %d * i + %d" lp.ic (4 * n + 4 * k) (4 * n) (4 * n + 4 * k))) SUBST1_TAC THENL
        [ARITH_TAC; FIRST_ASSUM ACCEPT_TAC];
       ALL_TAC] THEN
    (if !(ib_off ()) > 0 then (
       let off = 4 * n + 4 * k - !(ib_off ()) in
       let tm3 = parse_term(Printf.sprintf
         "read (memory :> bytes32 (word_add (word_add a (word %d)) (word (4 * (%d * i) + %d)))) s0 = (x:num->int32) (%d * i + %d)"
         !(ib_off ()) lp.ic off n (n + k)) in
       SUBGOAL_THEN tm3 ASSUME_TAC THENL
        [SUBGOAL_THEN (parse_term(Printf.sprintf
           "word_add (word_add a (word %d)) (word (4 * (%d * i) + %d)):int64 = word_add a (word (%d * i + %d))"
           !(ib_off ()) lp.ic off (4 * n) (4 * n + 4 * k))) SUBST1_TAC THENL
          [REWRITE_TAC[WORD_ADD; WORD_MUL] THEN CONV_TAC WORD_RULE; FIRST_ASSUM ACCEPT_TAC];
         ALL_TAC] THEN
       (let tm4 = parse_term(Printf.sprintf
         "read (memory :> bytes32 (word_add a (word (%d + (4 * (%d * i) + %d))))) s0 = (x:num->int32) (%d * i + %d)"
         !(ib_off ()) lp.ic off n (n + k)) in
        SUBGOAL_THEN tm4 ASSUME_TAC THENL
         [SUBGOAL_THEN (parse_term(Printf.sprintf
            "word_add a (word (%d + (4 * (%d * i) + %d))):int64 = word_add a (word (%d * i + %d))"
            !(ib_off ()) lp.ic off (4 * n) (4 * n + 4 * k))) SUBST1_TAC THENL
           [REWRITE_TAC[WORD_ADD; WORD_MUL] THEN CONV_TAC WORD_RULE; FIRST_ASSUM ACCEPT_TAC];
          ALL_TAC]))
     else ALL_TAC))) (0--(n-1)));;

let iblk_insts2 m bt =
  let (prev,unch,los,his) = iblk_insts m bt in
  let f th = CONV_RULE NORM_R_CONV (REWRITE_RULE[ADD1] th) in
  (f prev, f unch, map f los, map f his);;

let INTT_NEG4 = WORD_BLAST `word 18446744073709551612:int64 = word_neg (word 4)`;;

let iscal_loop_done lp =
  let n = lp.inn in
  let (prev,_,los,his) = iblk_insts2 lp.im `i + 1` in
  REWRITE_TAC[ARITH_RULE (parse_term(Printf.sprintf "%d * i + %d = (%d * i + %d) + %d" n (2 * n) n n n))] THEN
  ONCE_REWRITE_TAC[NTT_CHUNK_OUTPUT_SPLIT] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[prev] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> ihas_blocks (concl th) && is_forall (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[];
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NORM_R_CONV THEN
    REWRITE_TAC(los @ his) THEN ASM_REWRITE_TAC[] THEN TRY(CONV_TAC WORD_RULE)];;

let INTT_SUBSUC = prove
 (`!m i. i + 2 <= m ==> 4 * (m - (i + 1)) = 4 * (m - (i + 2)) + 4`,
  ARITH_TAC);;

let iscal_loop_final lp =
  let mi = (1 lsl lp.im) - 1 in
  let n = lp.inn and c = lp.ic in
  ENSURES_FINAL_STATE_TAC THEN CONV_TAC NORM_R_CONV THEN ASM_REWRITE_TAC[INTT_NEG4] THEN
  REPEAT CONJ_TAC THEN
  (fun gl ->
    let w = snd gl in
    if is_exists w then DISCHARGE_SAFETY_PROPERTY_TAC gl
    else if ihas_blocks w then iscal_loop_done lp gl
    else
      (TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
       TRY(MP_TAC (SPECL [mk_small_numeral mi; `i:num`] INTT_SUBSUC) THEN ANTS_TAC THENL [NUM_ASM_ARITH_TAC; DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th])] THEN
           REWRITE_TAC[WORD_ADD; WORD_MUL; INTT_NEG4] THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
       TRY(REWRITE_TAC[WORD_ADD; WORD_MUL; INTT_NEG4] THEN CONV_TAC WORD_RULE THEN NO_TAC)) gl);;

let INTT_ADDR_ASSOC = prove
 (`!a:int64 m p i n. word_add (word_add a (word m)) (word (p * i + n)) = word_add a (word (p * i + (m + n)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

let INTT_ADDR_FLAT = prove
 (`!a:int64 m p i n. word_add a (word (m + (p * i + n))) = word_add a (word (p * i + (m + n)))`,
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let iscal_loop_body lp nbody exec =
  let n = lp.inn and c = lp.ic in
  iscal_loop_prep lp THEN
  SUBGOAL_THEN (parse_term(Printf.sprintf "val(word_add (word (%d * i)) (word %d):int64) = %d * i + %d" c c c c)) ASSUME_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN NUM_ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (parse_term(Printf.sprintf "(%d * i + %d < %d) <=> (i + 1 < %d)" c c (c * (lp.inb - 1)) (lp.inb - 1))) ASSUME_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  iscal_loop_chunks lp THEN
  X86_STEPS_TAC exec (1--nbody) THEN
  (if !(ib_off ()) > 0 then (RULE_ASSUM_TAC(REWRITE_RULE[SPEC `a:int64` INTT_ADDR_ASSOC; SPEC `a:int64` INTT_ADDR_FLAT]) THEN RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_RED_CONV))) else ALL_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE iscal_post_rules) THEN NORM_R_ASM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE iscal_post_rules) THEN
  iscal_loop_final lp;;

let prove_iloop lp nbody =
  let g = parse_term(iscal_stmt lp) in
  prove(g, iscal_loop_skel (iscal_exec lp) lp (iscal_loop_body lp nbody (iscal_exec lp)));;

let prove_ifirst lp nbody =
  let g = parse_term(iscal_first_stmt lp) in
  let exec = iscal_exec lp in
  prove(g,
    META_EXISTS_TAC THEN MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `pc:num`; `zt:int64`; `x:num->int32`] THEN
    REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN FULL_INIT_TAC THEN
    iscal_first_prep lp THEN
    X86_STEPS_TAC exec (1--nbody) THEN
    RULE_ASSUM_TAC(REWRITE_RULE iscal_post_rules) THEN NORM_R_ASM_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE iscal_post_rules) THEN
    iscal_first_final lp);;

(* ------------------------------------------------------------------------- *)
(* The scaling loop. *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* The scaling loop of the inverse NTT: 2 coefficients per iteration, each   *)
(* multiplied by 41978 with a Montgomery reduction (mld_fqscale).            *)
(* ------------------------------------------------------------------------- *)

let SCALE_MONTRED = prove
 (`!a:int32. word_zx(word_ushr
       (word_add (word_mul (word_ishr (word_mul (word_sx a:int64) (word 0xff7fe3fa00000000)) 32)
                           (word 18446744073701171199))
                 (word_mul (word_sx a) (word 41978))) 32):int32 = mld_fqscale a`,
  GEN_TAC THEN REWRITE_TAC[mld_fqscale] THEN
  SUBGOAL_THEN `word_mul (word_sx (a:int32):int64) (word 0xff7fe3fa00000000) =
                word_mul (word_mul (word_sx a) (word 41978)) (word 252236767799803904)`
   SUBST1_TAC THENL
   [SUBGOAL_THEN `word 0xff7fe3fa00000000:int64 = word_mul (word 41978) (word 252236767799803904)` SUBST1_TAC THENL
     [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  MP_TAC(SPEC `word_mul (word_sx (a:int32):int64) (word 41978)` NTT_MONTRED_CLANG) THEN
  REWRITE_TAC[]);;

let iscale_mem_s st j = Printf.sprintf "read (memory :> bytes32 (word_add a (word (4 * %s)))) %s" j st;;

let iscale_regs ii =
  Printf.sprintf "read RDI s = a /\\ read RAX s = word 0xff7fe3fa00000000 /\\ read RCX s = word %s" ii;;

let iscale_stmt hd ex =
  Printf.sprintf
"exists f_events. forall e a pc (y:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    nonoverlapping (a,1024) (word pc,libmldsa_size)
    ==> ensures x86
     (\\s. bytes_loaded s (word pc) %s /\\
          read RIP s = word (pc + %d) /\\
          %s /\\
          (!j. j < 256 ==> %s = y j) /\\
          read events s = e)
     (\\s. read RIP s = word (pc + %d) /\\
          %s /\\
          (!j. j < 256 ==> %s = mld_fqscale (y j)) /\\
          (exists e2. read events s = APPEND e2 e /\\ e2 = f_events a pc /\\
              memaccess_inbounds e2 [a,1024] [a,1024]))
     (MAYCHANGE [RIP; RCX; RDX; RSI] ,, MAYCHANGE SOME_FLAGS ,,
      MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,1024)])"
   ntt_mc (!(ntt_fn_base ()) + hd) (iscale_regs "0") (iscale_mem_s "s" "j")
   (!(ntt_fn_base ()) + ex) (iscale_regs "256") (iscale_mem_s "s" "j");;

let iscale_inv ii =
  Printf.sprintf
   "%s /\\
    (!j. j < 2 * %s ==> %s = mld_fqscale (y j)) /\\
    (!j. 2 * %s <= j /\\ j < 256 ==> %s = y j)"
   (iscale_regs (Printf.sprintf "(2 * %s)" ii)) ii (iscale_mem_s "s" "j") ii (iscale_mem_s "s" "j");;

let iscale_skel exec hd ex body_tac =
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (pc:num).
        APPEND (f_ev_epil a pc)
         (APPEND (ENUMERATEL 128 (\i. f_ev_loop a pc i)) (f_ev_prol a pc))
      :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `pc:num`; `y:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `128`
   (parse_term(Printf.sprintf "pc + %d" (!(ntt_fn_base ()) + hd)))
   (parse_term(Printf.sprintf "pc + %d" (!(ntt_fn_base ()) + ex)))
   (parse_term(Printf.sprintf "\\i s. %s" (iscale_inv "i"))) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    (*** init ***)
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    (*** body ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    body_tac;
    (*** exit ***)
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_RED_CONV)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let iscale_prep =
  FULL_INIT_TAC THEN
  SUBGOAL_THEN `val(word (2 * i):int64) = 2 * i` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN NUM_ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `2 * (i + 1) <= 256` ASSUME_TAC THENL [NUM_ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [MATCH_MP (SPECL [`i:num`; `2`; `256`] NTT_CHUNK_IN_L) (ASSUME `2 * (i + 1) <= 256`)] o
     check (fun th -> aconv (concl th) (parse_term(Printf.sprintf "!j. 2 * i <= j /\\ j < 256 ==> %s = (y:num->int32) j" (iscale_mem_s "s0" "j"))))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  EVERY(map (fun k ->
    let addrs = if k = 0 then ["word_add a (word (4 * (2 * i)))"; "word_add a (word (8 * i))"]
                else [Printf.sprintf "word_add a (word (4 * (2 * i) + %d))" (4 * k); Printf.sprintf "word_add a (word (8 * i + %d))" (4 * k)] in
    EVERY(map (fun addr ->
      let tm = parse_term(Printf.sprintf "read (memory :> bytes32 (%s)) s0 = (y:num->int32) (2 * i + %d)" addr k) in
      let tm = if k = 0 then parse_term(Printf.sprintf "read (memory :> bytes32 (%s)) s0 = (y:num->int32) (2 * i)" addr) else tm in
      SUBGOAL_THEN tm ASSUME_TAC THENL
       [FIRST_ASSUM(MP_TAC o SPEC (mk_small_numeral k) o
          check (fun th -> can (term_match [] `!k. k < n ==> read (memory :> bytes32 (word_add a (word (4 * (n * i + k))))) s0 = y (n * i + k)`) (concl th))) THEN
        ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
        CONV_TAC NORM_R_CONV THEN DISCH_THEN(fun th -> MP_TAC th THEN CONV_TAC NORM_R_CONV THEN DISCH_THEN ACCEPT_TAC) ORELSE ALL_TAC;
        ALL_TAC]) addrs)) [0;1]);;

let SCALE_ADD_NEG_EQ_0 = prove
 (`!x y:int64. word_add x (word_neg y) = word 0 <=> x = y`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN SUBGOAL_THEN `x = word_add (word_add x (word_neg y)) y:int64` SUBST1_TAC THENL
     [CONV_TAC WORD_RULE; ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE];
    DISCH_THEN SUBST1_TAC THEN CONV_TAC WORD_RULE]);;

let SCALE_LOOP_COND = prove
 (`!i. i < 128 ==> (val(word_add (word (2 * i):int64) (word 18446744073709551362)) = 0 <=> i = 127)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_BLAST `word 18446744073709551362:int64 = word_neg (word 254)`; VAL_EQ_0; SCALE_ADD_NEG_EQ_0] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `(2 * i) MOD 2 EXP 64 = 2 * i /\ 254 MOD 2 EXP 64 = 254` (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 64 = 18446744073709551616`] THEN ASM_ARITH_TAC;
    ARITH_TAC]);;

let has_fqscale tm = can (find_term (fun t -> is_const t && fst(dest_const t) = "mld_fqscale")) tm;;

let iscale_done =
  ONCE_REWRITE_TAC[NTT_CHUNK_OUTPUT_SPLIT] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NORM_R_CONV THEN ASM_REWRITE_TAC[]];;

let iscale_final =
  ENSURES_FINAL_STATE_TAC THEN CONV_TAC NORM_R_CONV THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  (fun gl ->
    let w = snd gl in
    if is_exists w then DISCHARGE_SAFETY_PROPERTY_TAC gl
    else if has_fqscale w then iscale_done gl
    else
      (TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
       TRY(REWRITE_TAC[WORD_ADD; WORD_MUL] THEN CONV_TAC WORD_RULE THEN NO_TAC)) gl);;

let iscale_body nbody exec =
  iscale_prep THEN
  SUBGOAL_THEN `val(word_add (word (2 * i):int64) (word 18446744073709551362)) = 0 <=> i = 127` ASSUME_TAC THENL
   [MATCH_MP_TAC SCALE_LOOP_COND THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `i + 1 < 128 <=> ~(i = 127)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X86_STEPS_TAC exec (1--nbody) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SCALE_MONTRED; WORD_ZX_ZX_32_64_32]) THEN NORM_R_ASM_TAC THEN
  iscale_final;;

let prove_iscale hd ex nbody =
  let g = parse_term(iscale_stmt hd ex) in
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc [(!(ntt_fn_base ()) + hd, !(ntt_fn_base ()) + ex)] in
  prove(g, iscale_skel exec hd ex (iscale_body nbody exec));;

