(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Regions that clang 23 -O3 inlines into                                    *)
(* mldsa{44,65,87}_poly_uniform_eta_4x of the monolithic reduced-RAM build,  *)
(* as lemmas from a label of the code to another (see inline_sign.ml for the *)
(* form of the lemmas):                                                      *)
(*                                                                           *)
(*  - SCAN: the inlined mld_rej_eta_c on a buffer of buflen bytes in the     *)
(*    frame, at rsp0 + bo, for the polynomial at a whose first offset        *)
(*    coefficients are already there, as the gcc 12 -O2 reduced-RAM          *)
(*    rej_eta_NN_spec.ml states the function: the count of coefficients is   *)
(*    mld_rej_eta_ctr and the new ones are the first elements of             *)
(*    mld_rej_eta_list, with the events a function of the declassified       *)
(*    validity of the nibbles it reads (mld_rej_eta_declass). The loop reads *)
(*    one byte per iteration and leaves as soon as the count reaches 256.    *)
(*    Each function has eight scans: four in the first pass (one block of    *)
(*    each stream for eta = 2, two for eta = 4), which set a flag whether    *)
(*    the polynomial needs more, and four in the outer loop over the next    *)
(*    blocks.                                                                *)
(*  - ABS: the absorb of the four extended seeds of 66 bytes into the four   *)
(*    Keccak states that a memset has zeroed, with 16-, 2- and 1-byte XORs,  *)
(*    each state left as mld_keccak_absorb_once 136 0x1F 66 of its seed.     *)
(*  - GUARD: a scan of the outer loop with the test of its flag before it:   *)
(*    the code runs the scan only if the polynomial needs more coefficients  *)
(*    (offset < 256); else the count stays at 256.                           *)
(*                                                                           *)
(* The main proofs (inline_eta4x_top.ml) use these as subroutines.           *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_keypair.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_cp.ml";;
needs "x86/proofs/utils/mldsa_native_sampling.ml";;

(* ------------------------------------------------------------------------- *)
(* SCANF: the scans of the first pass for the polynomials 1 to 3 (eta = 2):  *)
(* loopN of the code with the count in creg, the pointer to the polynomial   *)
(* in preg, and setb freg after each byte (the flag whether the polynomial   *)
(* needs more, which the outer loop tests).                                  *)
(* ------------------------------------------------------------------------- *)

(* The scans differ in the index register ireg (RAX, or RBX for the first
   scan), where the pointer to the polynomial comes from (a register preg, or
   for the first scan the stack slot rsp0 + slot, which it reloads into RSI),
   and whether they set a flag register freg ("" for none: the scans of the
   outer loop, which test the count against 255 instead). *)

let scan_ptr_pre preg slot =
  if slot < 0 then Printf.sprintf "read %s s = a" preg
  else Printf.sprintf "read (memory :> bytes64 (word_add rsp0 (word %d))) s = a" slot;;

let SCAN_STMT fn loop exit eta bo buflen ireg creg preg slot freg =
  let flagpost = if freg = "" then "" else
    "word_zx(read @F@ s):byte =\n               (if mld_rej_eta_ctr @E@ 256 offset b @BL@ < 256 then word 1 else word 0) /\\\n" in
  let ptrpost = if slot < 0 then "read @P@ s = a /\\ " else "" in
  let nonov = if slot < 0 then "" else Printf.sprintf "; (word_add rsp0 (word %d),8)" slot in
  let mc = String.concat "; " (setify (["RIP"; "RAX"; "RCX"; "RDX"; "RSI"; ireg; creg] @ (if freg = "" then [] else [freg]))) in
  parse_term(subst_tokens
   ["@FLAGPOST@",flagpost; "@PTRPOST@",ptrpost; "@NONOV@",nonov; "@MCH@",mc;
    "@PTRPRE@",scan_ptr_pre preg slot;
    "@MC@",image_mc; "@FN@",fn; "@L@",loop; "@X@",exit; "@E@",string_of_int eta;
    "@BO@",string_of_int bo; "@BL@",string_of_int buflen; "@I@",ireg; "@C@",creg; "@P@",preg; "@F@",freg]
  "exists f_events.
   forall e a offset b pc rsp0.
     aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
     offset < 256 /\\
     ALL (nonoverlapping (word_add a (word(4 * offset)),4 * (256 - offset)))
         [(word pc,libmldsa_size); (word_add rsp0 (word @BO@),@BL@)@NONOV@]
     ==> ensures x86
          (\\s. bytes_loaded s (word pc) @MC@ /\\
               read RIP s = word (pc + @FN@_@L@) /\\
               read RSP s = rsp0 /\\ @PTRPRE@ /\\
               read @C@ s = word offset /\\ read @I@ s = word 0 /\\
               (!j. j < @BL@ ==> read(memory :> bytes8(word_add rsp0 (word(@BO@ + j)))) s = b j) /\\
               read events s = e)
          (\\s. read RIP s = word (pc + @FN@_@X@) /\\
               read RSP s = rsp0 /\\ @PTRPOST@
               read @C@ s = word(mld_rej_eta_ctr @E@ 256 offset b @BL@) /\\
               @FLAGPOST@               (!i. offset <= i /\\ i < mld_rej_eta_ctr @E@ 256 offset b @BL@
                    ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        EL (i - offset) (mld_rej_eta_list @E@ b (2 * @BL@))) /\\
               (exists e2.
                  read events s = APPEND e2 e /\\
                  e2 = f_events a offset rsp0 (mld_rej_eta_declass @E@ 256 offset b @BL@) pc /\\
                  memaccess_inbounds e2 [word_add rsp0 (word @BO@),@BL@@NONOV@]
                   [word_add a (word(4 * offset)),4 * (256 - offset)]))
          (MAYCHANGE [@MCH@] ,, MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(word_add a (word(4 * offset)),4 * (256 - offset))])");;

let SCANF_STMT fn loop exit eta bo buflen creg preg freg =
  SCAN_STMT fn loop exit eta bo buflen "RAX" creg preg (-1) freg;;

(*** The events: as REJ_ETA_44_TEMPLATE of the gcc proof, with the paths in
     which the count reaches 256 (and the loop exits at once) apart ***)

let SCAN_TEMPLATE =
 `\(a:int64) (offset:num) (rsp0:int64) (D:bool list) (pc:num).
   APPEND (f_ev_epil a offset rsp0 D pc)
    (APPEND
      (ENUMERATEL (LENGTH D DIV 2)
        (\i. if EL (2 * i) D
             then if EL (2 * i + 1) D
                  then if offset + LENGTH(FILTER (\x. x) (SUB_LIST(0,2 * i) D)) + 1 < 256
                       then if offset + LENGTH(FILTER (\x. x) (SUB_LIST(0,2 * i) D)) + 2 < 256
                            then f_ev_vv a offset rsp0 D pc i
                            else f_ev_vvf a offset rsp0 D pc i
                       else f_ev_vf a offset rsp0 D pc i
                  else if offset + LENGTH(FILTER (\x. x) (SUB_LIST(0,2 * i) D)) + 1 < 256
                       then f_ev_vx a offset rsp0 D pc i
                       else f_ev_vxf a offset rsp0 D pc i
             else if EL (2 * i + 1) D
                  then if offset + LENGTH(FILTER (\x. x) (SUB_LIST(0,2 * i) D)) + 1 < 256
                       then f_ev_xv a offset rsp0 D pc i
                       else f_ev_xvf a offset rsp0 D pc i
                  else f_ev_xx a offset rsp0 D pc i))
      (f_ev_prol a offset rsp0 D pc))
   :(uarch_event)list`;;

(*** For a loop whose fall-through at the last byte jumps once more to the
     exit (loop5 of the outer loop), the paths that do not fill the
     polynomial have two forms, i + 1 < buflen or not ***)

let SCAN_TEMPLATE_J buflen =
  let bl = mk_small_numeral buflen in
  let rec fix tm =
    match tm with
      Comb(Comb(Comb(Comb(Comb(Comb(Var(n,ty),x1),x2),x3),x4),x5),iv)
        when mem n ["f_ev_vv"; "f_ev_vx"; "f_ev_xv"; "f_ev_xx"] ->
        mk_cond(mk_binop `(<):num->num->bool` (mk_binop `(+):num->num->num` `i:num` `1`) bl, tm,
                list_mk_comb(mk_var(n ^ "e",ty),[x1;x2;x3;x4;x5;iv]))
    | Comb(f,x) -> mk_comb(fix f,fix x)
    | Abs(v,b) -> mk_abs(v,fix b)
    | _ -> tm in
  fix SCAN_TEMPLATE;;

let SCAN_INV eta bo buflen ireg creg preg slot freg =
  let flaginv = if freg = "" then "" else
    "(0 < i ==> word_zx(read @F@ s):byte =\n                    (if offset + MIN (256 - offset)\n                          (LENGTH(FILTER (\\x. x) (SUB_LIST(0,2 * i) D))) < 256\n                     then word 1 else word 0)) /\\\n         " in
  parse_term(subst_tokens
   ["@FLAGINV@",flaginv; "@PTRPRE@",scan_ptr_pre preg slot;
    "@E@",string_of_int eta; "@BO@",string_of_int bo; "@BL@",string_of_int buflen;
    "@I@",ireg; "@C@",creg; "@P@",preg; "@F@",freg]
  "\\i s. read RSP s = rsp0 /\\ @PTRPRE@ /\\
         (i < LENGTH (D:bool list) DIV 2 ==> read @I@ s = word i) /\\
         read @C@ s = word(offset + MIN (256 - offset)
                            (LENGTH(FILTER (\\x. x) (SUB_LIST(0,2 * i) D)))) /\\
         @FLAGINV@(!j. j < @BL@ ==> read(memory :> bytes8(word_add rsp0 (word(@BO@ + j)))) s = b j) /\\
         (!j. offset <= j /\\
              j < offset + MIN (256 - offset)
                            (LENGTH(FILTER (\\x. x) (SUB_LIST(0,2 * i) D)))
              ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                  EL (j - offset) (mld_rej_eta_list @E@ b (2 * i)))");;

let SCAN_EXEC fn loop exit = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))];;

(*** The declassified values D and the number M of bytes read, as in the gcc
     proof, for a count offset < 256 ***)

let SCAN_PRE_TAC eta buflen =
  let et = mk_small_numeral eta and bl = mk_small_numeral buflen in
  REWRITE_TAC[MLD_REJ_ETA_CTR] THEN
  MP_TAC(SPECL [et; `256`; `offset:num`; `b:num->byte`; bl] MLD_REJ_ETA_DECLASS) THEN
  MP_TAC(SPECL [et; `256`; `offset:num`; `b:num->byte`; bl;
    list_mk_comb(`mld_rej_eta_bytes`,[et; `256`; `offset:num`; `b:num->byte`; bl])]
    MLD_REJ_ETA_BYTES) THEN REWRITE_TAC[] THEN
  ABBREV_TAC (mk_eq(`D:bool list`,list_mk_comb(`mld_rej_eta_declass`,[et; `256`; `offset:num`; `b:num->byte`; bl]))) THEN
  ABBREV_TAC (mk_eq(`M:num`,list_mk_comb(`mld_rej_eta_bytes`,[et; `256`; `offset:num`; `b:num->byte`; bl]))) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `0 < M` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN MATCH_MP_TAC MLD_REJ_ETA_BYTES_POS THEN
    ASM_REWRITE_TAC[ARITH]; ALL_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `l = 2 * M ==> M = l DIV 2`) o
    check (fun th -> concl th = `LENGTH (D:bool list) = 2 * M`));;

(*** The nibbles of the byte b i = word nb, as the code computes them from the
     zero-extended byte in RCX: the registers whose value bit-blasts to one
     of the two nibbles are given the value word(nb MOD 16) or word(nb DIV
     16) of MLD_BYTE_NIBBLES ***)

let KS_NIB_TAC =
  let cands = [`word_zx(word_and ((b:num->byte) i) (word 15)):int64`;
               `word_zx(word_ushr ((b:num->byte) i) 4):int64`] in
  let regs = [`RAX`; `RCX`; `RDX`; `RSI`] in
  let bi = `(b:num->byte) i` in
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_eq c && (try mem (rand(rator(lhs c))) regs with Failure _ -> false) &&
       type_of(rhs c) = `:int64` then
      let v = rhs c in
      if not (free_in bi v) || subtract (frees v) (frees bi) <> [] || mem v cands then th else
      (try let cd = find (fun t -> can BITBLAST_RULE (mk_eq(v,t))) cands in
           let th1 = TRANS th (BITBLAST_RULE(mk_eq(v,cd))) in
           REWRITE_RULE[ASSUME `val((b:num->byte) i) = nb`] (REWRITE_RULE[MLD_BYTE_NIBBLES] th1)
       with Failure _ -> th)
    else th);;

(*** The flags of an 8-bit compare of the byte (CMP CL, imm for eta = 4), in
     terms of nb ***)

let KS_VAL_ZX_BYTE = prove
 (`!y:byte. val(word_zx(word_zx y:int32):int64) MOD 256 = val y`,
  GEN_TAC THEN MP_TAC(ISPEC `y:byte` VAL_BOUND) THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(y:byte) MOD 4294967296 = val y /\ val y MOD 18446744073709551616 = val y /\
                val y MOD 256 = val y` (fun th -> REWRITE_TAC[th]) THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let KS_FLAGS_NB_TAC =
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_iff c && can (term_match [] `read (f:(x86state,bool)component) s`) (lhand c) &&
       free_in `(b:num->byte) i` c
    then REWRITE_RULE[ASSUME `val((b:num->byte) i) = nb`] (REWRITE_RULE[KS_VAL_ZX_BYTE] th)
    else th);;

let KS_STEP_TAC execth n =
  SAMPLING_STEP_TAC execth n THEN KS_NIB_TAC THEN KS_FLAGS_NB_TAC THEN TRY SAMPLING_DECIDE_FLAGS_TAC THEN
  TRY SAMPLING_DECIDE_BRANCH_TAC;;

let rec KS_RUN_TAC execth n stop (asl,w) =
  (KS_STEP_TAC execth n THEN
   (fun g -> let pcv = SAMPLING_REGVAL `RIP` g in
             if is_cond pcv || mem pcv stop then ALL_TAC g
             else KS_RUN_TAC execth (n + 1) stop g)) (asl,w);;

(*** The simulation of the paths of an iteration: steps, deciding the
     branches by the assumptions, and splitting on the next of the case
     terms that decides the branch; it stops at the head or the exit of the
     loop (or a branch between the two) ***)

let rec KS_DRIVE_TAC execth stops cases n (asl,w) =
  let pcv = SAMPLING_REGVAL `RIP` (asl,w) in
  let is_stop t = mem t stops in
  if is_stop pcv || (is_cond pcv && is_stop (rand(rator pcv)) && is_stop (rand pcv))
  then ALL_TAC (asl,w)
  else if is_cond pcv then
    ((SAMPLING_DECIDE_BRANCH_TAC THEN KS_DRIVE_TAC execth stops cases n) ORELSE
     (fun (asl,w) ->
        let decided t = exists (fun (_,th) -> let c = concl th in c = t || c = mk_neg t) asl in
        (* a test of the position alone (the loop test) is decided by the
           cases about the position, the others by the rest *)
        let p = lhand(rator pcv) in
        let posonly t = subtract (frees t) [`i:num`] = [] in
        let relevant t = if posonly p then posonly t else not (posonly t) in
        let t = try find (fun t -> not (decided t) && relevant t) cases
                with Failure _ -> failwith "KS_DRIVE_TAC: no case decides the branch" in
        let is_el = (try fst(dest_const(fst(strip_comb t))) = "EL" with Failure _ -> false) in
        ((if is_el then SAMPLING_CASES_TAC t else ASM_CASES_TAC t) THEN
         KS_DRIVE_TAC execth stops cases n) (asl,w))) (asl,w)
  else (KS_STEP_TAC execth n THEN KS_DRIVE_TAC execth stops cases (n + 1)) (asl,w);;

(*** The coefficient for eta = 2 as clang computes it from the nibble t
     (t * 205 >> 10, the LEA for 5 times it, and 2 + 5 q - t) ***)

let KS_ETA2_COEFF = prove
 (`!t. t < 16
       ==> word_add
            (word_sub
              (word_sx
                (word_add
                  (word_zx (word_ushr (word_mul (word t:int32) (word 205)) 10):int64)
                  (word (4 * val (word_zx (word_ushr
                     (word_mul (word t:int32) (word 205)) 10):int64)))))
              (word t))
            (word 2):int32 =
           word_sub (word 2)
            (word_sub (word t)
              (word_mul (word_ushr (word_mul (word 205) (word t)) 10) (word 5)))`,
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(REPEATC(CHANGED_CONV(NUM_REDUCE_CONV THENC WORD_REDUCE_CONV))));;

(*** The coefficients after iteration i: those before, and the new ones, as
     REJ_ETA_44_STORE_TAC of the gcc proof ***)

let KS_STORE_TAC eta =
  let lst = parse_term(Printf.sprintf "LENGTH (mld_rej_eta_list %d b (2 * i)) = c" eta) in
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[APPEND] THEN
  ASM_CASES_TAC `j < offset + c` THENL
   [REWRITE_TAC[EL_APPEND; ASSUME lst] THEN
    SUBGOAL_THEN `j - offset < c` (fun th -> REWRITE_TAC[th]) THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && free_in `bytes32` (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `j = (offset + c) + 0 \/ j = (offset + c) + 1`
   (DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [SIMPLE_ARITH_TAC; ALL_TAC; ALL_TAC] THEN
  TRY(SUBGOAL_THEN `F` CONTR_TAC THEN SIMPLE_ARITH_TAC THEN NO_TAC) THEN
  REWRITE_TAC[EL_APPEND; ASSUME lst;
              ARITH_RULE `((offset + c) + k) - offset = c + k`;
              ARITH_RULE `~(c + k < c)`; ARITH_RULE `(c + k) - c = k`] THEN
  CONV_TAC(RAND_CONV SAMPLING_EL_LIST_CONV) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN ASM_REWRITE_TAC[];;

(*** The end of a path: the loop test, the invariant for i + 1 and the
     events, as REJ_ETA_44_PATH_TAC of the gcc proof ***)

let KS_END_TAC eta coeffths looppc =
  SAMPLING_COND_REWRITE_TAC coeffths THEN
  TRY(SAMPLING_LOOP_PC_TAC `LENGTH (D:bool list) DIV 2`
       [SYM(ASSUME `M = LENGTH (D:bool list) DIV 2`)] ORELSE
      SAMPLING_LOOP_EXIT_TAC `LENGTH (D:bool list) DIV 2`
       [SYM(ASSUME `M = LENGTH (D:bool list) DIV 2`)] looppc) THEN
  TRY(SUBGOAL_THEN `i + 1 < LENGTH (D:bool list) DIV 2` ASSUME_TAC THENL
       [REWRITE_TAC[SYM(ASSUME `M = LENGTH (D:bool list) DIV 2`)] THEN
        ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; ALL_TAC]) THEN
  TRY(SUBGOAL_THEN `~(i + 1 < LENGTH (D:bool list) DIV 2)` ASSUME_TAC THENL
       [REWRITE_TAC[SYM(ASSUME `M = LENGTH (D:bool list) DIV 2`)] THEN
        ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; ALL_TAC]) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_iff(concl th) && lhand(concl th) = `i + 1 < M`)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SAMPLING_W64_TAC THEN SAMPLING_SELECT_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(AP_TERM_TAC THEN SIMPLE_ARITH_TAC THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(KS_STORE_TAC eta THEN NO_TAC) THEN
  TRY(DISCH_TAC THEN REWRITE_TAC[SAMPLING_JOIN_BYTE] THEN
      REPEAT COND_CASES_TAC THEN REWRITE_TAC[] THEN
      CONV_TAC WORD_REDUCE_CONV THEN SIMPLE_ARITH_TAC THEN NO_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `c:num` &&
    can (term_match [] `LENGTH(FILTER (\x:bool. x) l)`) (lhs(concl th)))) THEN
  SAMPLING_PATH_DISCHARGE_TAC;;

(*** The setup of iteration i, as REJ_ETA_44_BODY_SETUP_TAC of the gcc proof,
     with the flag register as a ghost (SETcc writes its low byte only) ***)

let KS_BODY_SETUP_TAC eta buflen ireg freg =
  let et = mk_small_numeral eta and bl = mk_small_numeral buflen in
  let lst k = list_mk_comb(`mld_rej_eta_list`,[et; `b:num->byte`; k]) in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `i < M` ASSUME_TAC THENL
   [UNDISCH_TAC `i < LENGTH (D:bool list) DIV 2` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `i < M`) o
    check (fun th -> is_forall(concl th) && can (term_match [] `!m. m < M ==> P m`) (concl th))) THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `2 * i` o
    check (fun th -> is_forall(concl th) && can (term_match [] `!n. n <= 2 * M ==> P n`) (concl th))) THEN
  ANTS_TAC THENL [UNDISCH_TAC `i < M` THEN ARITH_TAC; DISCH_TAC] THEN
  (if freg = "" then ALL_TAC else GHOST_INTRO_TAC `fl_g:int64` (parse_term("read " ^ freg))) THEN
  FULL_INIT_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_imp(concl th) && free_in (mk_const(ireg,[])) (concl th) &&
                             free_in `word i:int64` (concl th)
                 then ASSUME_TAC(MP th (ASSUME `i < LENGTH (D:bool list) DIV 2`)) else NO_TAC) THEN
  ABBREV_TAC `c = LENGTH(FILTER (\x. x) (SUB_LIST (0,2 * i) (D:bool list)))` THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) && lhs(concl th) = `c:num`)) THEN
  SUBGOAL_THEN `offset + c < 256` ASSUME_TAC THENL
   [UNDISCH_TAC (mk_binop `(<):num->num->bool` (mk_binop `(+):num->num->num` `offset:num`
                   (mk_comb(`LENGTH:(int32)list->num`,lst `2 * i`))) `256`) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `MIN (256 - offset) c = c` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [UNDISCH_TAC `offset + c < 256` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME (mk_binop `(<):num->num->bool` `i:num` bl)) o SPEC `i:num` o
    check (fun th -> is_forall(concl th) && free_in `bytes8` (concl th))) THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `2 * (i + 1)` o
    check (fun th -> is_forall(concl th) && can (term_match [] `!n. n <= 2 * M ==> P n`) (concl th))) THEN
  ANTS_TAC THENL [UNDISCH_TAC `i < M` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(MATCH_MP MLD_REJ_ETA_BYTES_NEXT
   (CONJ (ASSUME (mk_eq(list_mk_comb(`mld_rej_eta_bytes`,[et; `256`; `offset:num`; `b:num->byte`; bl]),`M:num`)))
         (ASSUME `i < M`))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `2 * i + 1` o
    check (fun th -> is_forall(concl th) && can (term_match [] `!k. k < 2 * M ==> P k`) (concl th))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `2 * i` o
    check (fun th -> is_forall(concl th) && can (term_match [] `!k. k < 2 * M ==> P k`) (concl th))) THEN
  REWRITE_TAC[ARITH_RULE `2 * i < 2 * M <=> i < M`; ARITH_RULE `2 * i + 1 < 2 * M <=> i < M`; ASSUME `i < M`] THEN
  REWRITE_TAC[MLD_REJ_ETA_LIST_BYTE; LENGTH_APPEND; SAMPLING_LENGTH_COND;
              MLD_REJ_ETA_VALID_BYTE; mld_rej_eta_coeff;
              ASSUME (mk_eq(mk_comb(`LENGTH:(int32)list->num`,lst `2 * i`),`c:num`))] THEN
  MP_TAC(ISPEC `(b:num->byte) i` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ABBREV_TAC `nb = val((b:num->byte) i)` THEN REPEAT DISCH_TAC THEN
  VAL_INT64_TAC `i:num`;;

let KS_CASES = [`EL (2 * i) (D:bool list)`; `EL (2 * i + 1) (D:bool list)`;
                `offset + c + 1 < 256`; `offset + c + 2 < 256`];;

(*** The return from the loop after M bytes: the count, the flag and the
     coefficients, as in the gcc proof ***)

let KS_EXIT_TAC eta buflen =
  let et = mk_small_numeral eta and bl = mk_small_numeral buflen in
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPEC `2 * M` o
    check (fun th -> is_forall(concl th) && can (term_match [] `!n. n <= 2 * M ==> P n`) (concl th))) THEN
  REWRITE_TAC[LE_REFL; ASSUME `M = LENGTH (D:bool list) DIV 2`] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM(ASSUME `M = LENGTH (D:bool list) DIV 2`); ASSUME `0 < M`]) THEN
  REWRITE_TAC[GSYM(ASSUME `M = LENGTH (D:bool list) DIV 2`)] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MP_TAC(SPECL [et; `b:num->byte`; `2 * M`; mk_binop `( * ):num->num->num` `2` bl; `j - offset`]
      EL_MLD_REJ_ETA_LIST_PREFIX) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [UNDISCH_TAC (mk_binop `(<=):num->num->bool` `M:num` bl) THEN ARITH_TAC; SIMPLE_ARITH_TAC];
      DISCH_THEN SUBST1_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let SCAN_TAC_G template cases fn loop exit eta bo buflen ireg creg preg slot freg coeffths =
  let execth = SCAN_EXEC fn loop exit in
  let pcw l = parse_term(Printf.sprintf "word(pc + %d):int64" (layout (fn ^ "_" ^ l))) in
  let looppc = pcw loop and exitpc = pcw exit in
  CONCRETIZE_F_EVENTS_TAC template THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `offset:num`; `b:num->byte`; `pc:num`; `rsp0:int64`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN SCAN_PRE_TAC eta buflen THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `LENGTH (D:bool list) DIV 2`
   (parse_term(Printf.sprintf "pc + %s_%s" fn loop)) (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (SCAN_INV eta bo buflen ireg creg preg slot freg) THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `M = LENGTH (D:bool list) DIV 2`)) THEN
    UNDISCH_TAC `0 < M` THEN ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES; FILTER; LENGTH; LT_REFL;
                ARITH_RULE `MIN a 0 = 0`; ADD_CLAUSES; WORD_ADD_0;
                ARITH_RULE `~(a <= j /\ j < a)`] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    KS_BODY_SETUP_TAC eta buflen ireg freg THEN
    SUBGOAL_THEN (parse_term(Printf.sprintf
      "word_add rsp0 (word (1 * i + %d)):int64 = word_add rsp0 (word (%d + i))" bo bo))
      ASSUME_TAC THENL [CP_ALIAS64_TAC; ALL_TAC] THEN
    X86_STEPS_TAC execth (1--3) THEN KS_NIB_TAC THEN
    KS_STEP_TAC execth 4 THEN KS_STEP_TAC execth 5 THEN
    KS_DRIVE_TAC execth [looppc; exitpc] cases 6 THEN
    KS_END_TAC eta coeffths looppc;
    KS_EXIT_TAC eta buflen];;

let SCAN_TAC = SCAN_TAC_G SCAN_TEMPLATE KS_CASES;;

let PROVE_SCAN fn loop exit eta bo buflen ireg creg preg slot freg coeffths =
  prove(SCAN_STMT fn loop exit eta bo buflen ireg creg preg slot freg,
        SCAN_TAC fn loop exit eta bo buflen ireg creg preg slot freg coeffths);;

(* the scan whose last byte falls through to a jump to the exit *)
let PROVE_SCAN_J fn loop exit eta bo buflen ireg creg preg slot freg coeffths =
  let cases = KS_CASES @ [parse_term(Printf.sprintf "i + 1 < %d" buflen)] in
  prove(SCAN_STMT fn loop exit eta bo buflen ireg creg preg slot freg,
        SCAN_TAC_G (SCAN_TEMPLATE_J buflen) cases fn loop exit eta bo buflen ireg creg preg slot freg coeffths);;

let PROVE_SCANF fn loop exit eta bo buflen creg preg freg coeffths =
  PROVE_SCAN fn loop exit eta bo buflen "RAX" creg preg (-1) freg coeffths;;

(* ------------------------------------------------------------------------- *)
(* The eight scans of mldsa44_poly_uniform_eta_4x and of                     *)
(* mldsa87_poly_uniform_eta_4x (eta = 2), whose code is the same: the first  *)
(* pass over the first block of each of the four streams (the first scan     *)
(* with the pointer in the stack slot rsp0 + 0x38 and RBX as position, the   *)
(* others with flags), and the four scans of the outer loop over each next   *)
(* block, the first with the jump to the exit at the end.                    *)
(* ------------------------------------------------------------------------- *)

let PROVE_ETA2_SCANS fn =
  let c = [KS_ETA2_COEFF] in
  [PROVE_SCAN fn "join1" "join5" 2 0x4e0 136 "RBX" "R13" "RSI" 56 "R11" c;
   PROVE_SCANF fn "loop1" "loop1_exit" 2 0x580 136 "RBX" "R9" "R10" c;
   PROVE_SCANF fn "loop2" "loop2_exit" 2 0x620 136 "R14" "R8" "R9" c;
   PROVE_SCANF fn "loop3" "loop3_exit" 2 0x6c0 136 "R15" "RDI" "RCX" c;
   PROVE_SCAN_J fn "loop5" "join17" 2 0x4e0 136 "RAX" "R13" "R10" (-1) "" c;
   PROVE_SCAN fn "loop6" "loop6_exit" 2 0x580 136 "RAX" "RBX" "R9" (-1) "" c;
   PROVE_SCAN fn "loop7" "loop7_exit" 2 0x620 136 "RAX" "R14" "R8" (-1) "" c;
   PROVE_SCAN fn "loop8" "loop8_exit" 2 0x6c0 136 "RAX" "R15" "RDI" (-1) "" c];;

(* The eight scans of mldsa65_poly_uniform_eta_4x (eta = 4): the first pass
   reads two blocks (272 bytes) of each stream, and the outer loop is loop4
   to loop7, the first with the jump to the exit at the end. *)

let PROVE_ETA4_SCANS fn =
  [PROVE_SCAN fn "join1" "join5" 4 0x4e0 272 "RBX" "R13" "RSI" 56 "R11" [];
   PROVE_SCANF fn "loop1" "loop1_exit" 4 0x600 272 "RBX" "R9" "R10" [];
   PROVE_SCANF fn "loop2" "loop2_exit" 4 0x720 272 "R14" "R8" "R9" [];
   PROVE_SCANF fn "loop3" "loop3_exit" 4 0x840 272 "R15" "RDI" "RCX" [];
   PROVE_SCAN_J fn "loop4" "join19" 4 0x4e0 136 "RAX" "R13" "R10" (-1) "" [];
   PROVE_SCAN fn "loop5" "loop5_exit" 4 0x600 136 "RAX" "RBX" "R9" (-1) "" [];
   PROVE_SCAN fn "loop6" "loop6_exit" 4 0x720 136 "RAX" "R14" "R8" (-1) "" [];
   PROVE_SCAN fn "loop7" "loop7_exit" 4 0x840 136 "RAX" "R15" "RDI" (-1) "" []];;

(* ------------------------------------------------------------------------- *)
(* ABS: the absorb of the four extended seeds of 66 bytes into the four      *)
(* states zeroed by the memset before it.                                    *)
(* ------------------------------------------------------------------------- *)

let ABS_ST = [448; 648; 848; 1048] and ABS_EXT = [64; 160; 256; 352];;

let ABS_STMT start exit regs =
  let regpost = String.concat " /\\\n               "
    (map (fun (r,off) -> Printf.sprintf "read %s s = word_add fb (word %d)" r off) regs) in
  let mch = String.concat "; " (map fst regs) in
  parse_term(subst_tokens
   ["@MC@",image_mc; "@S@",string_of_int start; "@X@",string_of_int exit;
    "@RP@",regpost; "@MCH@",mch]
  "exists f_events.
   forall e fb M0 M1 M2 M3 pc.
     aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
     aligned 32 (fb:int64) /\\
     nonoverlapping (word pc,libmldsa_size) (word_add fb (word 64),1184)
     ==> ensures x86
          (\\s. bytes_loaded s (word pc) @MC@ /\\
               read RIP s = word (pc + @S@) /\\
               read RSP s = fb /\\
               read (memory :> bytes(word_add fb (word 64),66)) s = M0 /\\
               read (memory :> bytes(word_add fb (word 160),66)) s = M1 /\\
               read (memory :> bytes(word_add fb (word 256),66)) s = M2 /\\
               read (memory :> bytes(word_add fb (word 352),66)) s = M3 /\\
               read (memory :> bytes(word_add fb (word 448),800)) s = 0 /\\
               read events s = e)
          (\\s. read RIP s = word (pc + @X@) /\\
               read RSP s = fb /\\ @RP@ /\\
               read (memory :> bytes(word_add fb (word 448),200)) s =
               val(mld_keccak_absorb_once 136 31 66 M0) /\\
               read (memory :> bytes(word_add fb (word 648),200)) s =
               val(mld_keccak_absorb_once 136 31 66 M1) /\\
               read (memory :> bytes(word_add fb (word 848),200)) s =
               val(mld_keccak_absorb_once 136 31 66 M2) /\\
               read (memory :> bytes(word_add fb (word 1048),200)) s =
               val(mld_keccak_absorb_once 136 31 66 M3) /\\
               (exists e2. read events s = APPEND e2 e /\\
                  e2 = f_events fb pc /\\
                  memaccess_inbounds e2
                   [word_add fb (word 64),1184]
                   [word_add fb (word 448),800]))
          (MAYCHANGE [RIP; RAX; @MCH@] ,, MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(word_add fb (word 448),800)])");;

(*** word((M DIV 2^(8j)) MOD 2^N) as a subword of word M : 528 word ***)

let ABS_SUBW n =
  let sub = subst_tokens ["@N@",string_of_int n;
    "@NT@",(match n with 8 -> ":byte" | 16 -> ":int16" | 64 -> ":int64" | _ -> ":int128")] in
  prove(parse_term(sub
   "!M j. M < 2 EXP 528 /\\ 8 * j + @N@ <= 528
         ==> word((M DIV 2 EXP (8 * j)) MOD 2 EXP @N@)@NT@ =
             word_subword (word M:528 word) (8 * j,@N@)"),
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; VAL_WORD_SUBWORD; DIMINDEX_8; DIMINDEX_16; DIMINDEX_64; DIMINDEX_128] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  SUBGOAL_THEN `M MOD 2 EXP 528 = M` (fun th -> REWRITE_TAC[th]) THENL [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MIN; MOD_MOD_REFL] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL]);;

let ABS_SUBW16 = ABS_SUBW 16 and ABS_SUBW128 = ABS_SUBW 128;;

let KP_RD16 = KP_RDN 16;;

(*** The bytes16 at a is the low part of the bytes128 at a ***)

let ABS_B16_OF_128 = prove
 (`!a:int64 s:x86state.
     read (memory :> bytes16 a) s = word_zx(read (memory :> bytes128 a) s)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; BYTES128_WBYTES; BYTES16_WBYTES;
              READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              DIMINDEX_16; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  MP_TAC(SPECL [`a:int64`; `16`;
                `read (memory :> bytes(a:int64,16)) (s:x86state)`;
                `0`; `2`; `s:x86state`] READ_MEMORY_BYTES_SUB) THEN
  REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DIV_1]);;

(*** The absorbed state of 66 bytes as a 1600-bit word ***)

let ABS_SW = `word_or (word_zx (word M:528 word):1600 word) (word(2 EXP 528 * 31 + 2 EXP 1080 * 128))`;;

let ABS_ABSORB_VAL = prove
 (`!M. M < 2 EXP 528
       ==> val(mld_keccak_absorb_once 136 31 66 M:1600 word) =
           M + 2 EXP 528 * 31 + 2 EXP 1080 * 128`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[MLD_KECCAK_ABSORB_ONCE] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  REWRITE_TAC[keccak_absorb; WORD_XOR_0; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  SIMP_TAC[MLD_KECCAK_PAD_SHORT; ARITH_RULE `66 + 2 <= 136`; ARITH_RULE `31 < 256`] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1] THEN
  SUBGOAL_THEN `(M + 2 EXP (8 * 66) * (31 + 2 EXP (8 * (136 - 66 - 1)) * 128)) = M + 2 EXP 528 * 31 + 2 EXP 1080 * 128` SUBST1_TAC THENL
   [REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM EXP_ADD; ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `(M + 2 EXP 528 * 31 + 2 EXP 1080 * 128) < 2 EXP 1088` ASSUME_TAC THENL
   [UNDISCH_TAC `M < 2 EXP 528` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `8 * 136 = 1088`] THEN ASM_SIMP_TAC[MOD_LT] THEN MATCH_MP_TAC MOD_LT THEN
  FIRST_ASSUM(fun th -> MP_TAC th) THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let ABS_S_WORD = prove
 (`!M. M < 2 EXP 528
       ==> mld_keccak_absorb_once 136 31 66 M =
           word_or (word_zx (word M:528 word):1600 word)
                   (word(2 EXP 528 * 31 + 2 EXP 1080 * 128))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  ASM_SIMP_TAC[ABS_ABSORB_VAL] THEN
  SUBGOAL_THEN `(word_zx (word M:528 word):1600 word) || word (2 EXP 528 * 31 + 2 EXP 1080 * 128) = word_add (word_zx (word M:528 word):1600 word) (word (2 EXP 528 * 31 + 2 EXP 1080 * 128))` SUBST1_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_CONV `dimindex(:1600)`; DIMINDEX_CONV `dimindex(:528)`] THEN
  SUBGOAL_THEN `M MOD 2 EXP 528 = M` SUBST1_TAC THENL [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `MIN 528 1600 = 528`] THEN
  SUBGOAL_THEN `M MOD 2 EXP 528 = M` SUBST1_TAC THENL [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `M < 2 EXP 1600 /\ 2 EXP 528 * 31 + 2 EXP 1080 * 128 < 2 EXP 1600 /\ M + 2 EXP 528 * 31 + 2 EXP 1080 * 128 < 2 EXP 1600` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `M < 2 EXP 528` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT]);;

(*** A piece of the state S in memory (bytes16), and a zero piece ***)

let ABS_PIECE2 = prove
 (`!(S:1600 word) (A:int64) (s:x86state) (V:int16) off.
     read (memory :> bytes16 A) s = V /\ V = word_subword S (8 * off,16)
     ==> read (memory :> bytes(A,2)) s = (val S DIV 2 EXP (8 * off)) MOD 2 EXP 16`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[KP_B2] THEN ASM_REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_CONV `dimindex(:16)`; MIN; LE_REFL] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let ABS_PIECEZ = prove
 (`!(S:1600 word) (A:int64) (s:x86state) off n.
     read (memory :> bytes(A,n)) s = 0 /\ 8 * off + 8 * n <= 1600 /\
     word_subword S (8 * off,8 * n):1600 word = word 0
     ==> read (memory :> bytes(A,n)) s = (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * n)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `val:1600 word->num`) THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD_0; DIMINDEX_CONV `dimindex(:1600)`] THEN
  SUBGOAL_THEN `MIN (8 * n) 1600 = 8 * n` SUBST1_TAC THENL
   [UNDISCH_TAC `8 * off + 8 * n <= 1600` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC);;

(*** A piece of the state: bytes128, bytes16, bytes8 facts with the value
     V of the simulation, or a zero region (len > 16 or the zero pieces) ***)

let ABS_PIECE_THM sw base asl sn off len zero =
  let s = mk_var(sn,`:x86state`) in
  let a = parse_term(Printf.sprintf "word_add fb (word %d):int64" (base + off)) in
  if zero then
    let ftm = parse_term(Printf.sprintf "read (memory :> bytes(word_add fb (word %d),%d)) %s = 0" (base + off) len sn) in
    let fact = try snd(find (fun (_,th) -> concl th = ftm) asl)
               with Failure _ -> failwith ("ABS_PIECE_THM: no fact "^string_of_term ftm) in
    let inst = SPECL [sw; a; s; mk_small_numeral off; mk_small_numeral len] ABS_PIECEZ in
    let ants = conjuncts(fst(dest_imp(concl inst))) in
    let th2 = EQT_ELIM(NUM_REDUCE_CONV (el 1 ants)) in
    let th3 = prove(el 2 ants, CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST) in
    MP inst (CONJ fact (CONJ th2 th3))
  else
  let sz,lem = match len with 16 -> "bytes128",KP_PIECE16 | 2 -> "bytes16",ABS_PIECE2 | _ -> "bytes8",KP_PIECE8 in
  let ftm = parse_term(Printf.sprintf "read (memory :> %s (word_add fb (word %d))) %s" sz (base + off) sn) in
  let fact = try snd(find (fun (_,th) -> let c = concl th in is_eq c && lhs c = ftm) asl)
             with Failure _ -> failwith ("ABS_PIECE_THM: no fact "^string_of_term ftm) in
  let v = rhs(concl fact) in
  let inst = SPECL [sw; a; s; v; mk_small_numeral off] lem in
  let eqt = snd(dest_conj(fst(dest_imp(concl inst)))) in
  let eqth = prove(eqt, CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[KP_ZX_MOD8] THEN CONV_TAC WORD_BLAST) in
  MP inst (CONJ fact eqth);;

(* pieces (off,len,zero) of one state, at the base of the state *)
let ABS_PIECES =
  [0,16,false; 16,16,false; 32,16,false; 48,16,false; 64,2,false; 66,1,false;
   67,68,true; 135,1,false; 136,64,true];;

let ABS_CHAIN_TAC sw base sn =
  W(fun (asl,w) ->
    let s = mk_var(sn,`:x86state`) in
    let d = parse_term(Printf.sprintf "word_add fb (word %d):int64" base) in
    let x = mk_comb(`val:1600 word->num`,sw) in
    let cur0 = KP_NORM(prove(
      subst [s,`s:x86state`; x,`x:num`; d,`d:int64`]
       `read (memory :> bytes(d,0)) s = x MOD 2 EXP (8 * 0)`,
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; MULT_CLAUSES; EXP; MOD_1])) in
    let step (cur,j) (off,len,zero) =
      assert (off = j);
      let pth = KP_NORM(ABS_PIECE_THM sw base asl sn off len zero) in
      let ext = KP_NORM(SPECL [d; mk_small_numeral j; mk_small_numeral len; x; s] KP_BYTES_EXTEND) in
      (MP ext (CONJ cur pth), j + len) in
    let fin,n = rev_itlist (fun p st -> step st p) ABS_PIECES (cur0,0) in
    ASSUME_TAC(REWRITE_RULE[KP_MODLEMMA] fin));;

(*** Setup facts: alignment, the chunks of the inputs, the ghosts of the
     16-byte reads past the inputs, and the zero facts of the states ***)

let ABS_ALIGNED_TAC offs =
  SUBGOAL_THEN `aligned 16 (fb:int64)` ASSUME_TAC THENL
   [MATCH_MP_TAC(MP (ISPECL [`16`;`32`;`fb:int64`] ALIGNED_WORD_WEAKEN)
                    (EQT_ELIM(DIVIDES_CONV `16 divides 32`))) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY (fun off ->
    SUBGOAL_THEN (subst [mk_small_numeral off,`n:num`] `aligned 16 (word_add (fb:int64) (word n))`) ASSUME_TAC THENL
     [MATCH_MP_TAC ALIGNED_WORD_ADD THEN ASM_REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[];
      ALL_TAC]) offs;;

(* fact th of bytes(a,m) = x, k + nb <= m: bytesN at a + k from KP_RDN       *)
let abs_sub_fact rd th k nb =
  let c = concl th in
  let a,m = dest_pair(rand(rand(lhand(lhs c)))) in
  let x = rhs c in
  let s = rand(lhs c) in
  let ant = mk_binary "<=" (mk_binary "+" (mk_small_numeral k,mk_small_numeral nb),m) in
  KP_NORM(MP (SPECL [a; m; x; mk_small_numeral k; s] rd) (CONJ th (EQT_ELIM(NUM_REDUCE_CONV ant))));;

let ABS_INPUT_TAC sname =
  MAP_EVERY (fun (i,e) ->
    let mv = mk_var("M"^string_of_int i,`:num`) in
    let ftm = subst [mk_small_numeral e,`e:num`; mv,`M:num`; mk_var(sname,`:x86state`),`s:x86state`]
               `read (memory :> bytes(word_add fb (word e),66)) s = M` in
    let bnd = subst [mv,`M:num`] `M < 2 EXP 528` in
    SUBGOAL_THEN bnd ASSUME_TAC THENL
     [MP_TAC(ISPECL [subst [mk_small_numeral e,`e:num`] `word_add fb (word e):int64`; `66`;
                     subst [mk_var(sname,`:x86state`),`s:x86state`] `read memory (s:x86state)`] READ_BYTES_BOUND) THEN
      REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; ASSUME ftm] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    (fun g ->
      let th = ASSUME ftm in
      let chunk q =
        let th1 = abs_sub_fact KP_RD128 th (16 * q) 16 in
        let th2 = MP (SPECL [mv; mk_small_numeral (16 * q)] ABS_SUBW128)
                     (CONJ (ASSUME bnd) (EQT_ELIM(NUM_REDUCE_CONV (mk_binary "<=" (mk_binary "+" (mk_binary "*" (`8`,mk_small_numeral (16*q)),`128`),`528`))))) in
        KP_NORM(TRANS th1 (KP_NORM th2)) in
      let th16 =
        let th1 = abs_sub_fact KP_RD16 th 64 2 in
        let th2 = MP (SPECL [mv; `64`] ABS_SUBW16)
                     (CONJ (ASSUME bnd) (EQT_ELIM(NUM_REDUCE_CONV `8 * 64 + 16 <= 528`))) in
        KP_NORM(TRANS th1 (KP_NORM th2)) in
      (MAP_EVERY (fun q -> ASSUME_TAC(chunk q)) (0--3) THEN
       ASSUME_TAC th16) g)) (zip (0--3) ABS_EXT);;

(* the 16-byte reads at ext + 64 as ghosts g0..g3 (before the init), and
   their low 16 bits (after it) *)
let ABS_GHOST_TAC =
  MAP_EVERY (fun (i,e) ->
    GHOST_INTRO_TAC (mk_var("g"^string_of_int i,`:int128`))
      (parse_term(Printf.sprintf "read (memory :> bytes128 (word_add fb (word %d)))" (e + 64))))
   (zip (0--3) ABS_EXT);;

let ABS_G16_TAC sname =
  MAP_EVERY (fun (i,e) ->
    let gv = mk_var("g"^string_of_int i,`:int128`) in
    let a = parse_term(Printf.sprintf "word_add fb (word %d):int64" (e + 64)) in
    (fun (asl,w) ->
      let s = mk_var(sname,`:x86state`) in
      let b16 = SPECL [a; s] ABS_B16_OF_128 in
      let gfact = find (fun th -> let c = concl th in is_eq c && rhs c = gv && lhs c = rand(rhs(concl b16))) (map snd asl) in
      let b16fact = find (fun th -> let c = concl th in is_eq c && lhs c = lhs(concl b16)) (map snd asl) in
      ASSUME_TAC(TRANS (SYM(REWRITE_RULE[gfact] b16)) b16fact) (asl,w))) (zip (0--3) ABS_EXT);;

(* the zero facts of state k at base b from the 800 zero bytes at fb + 448   *)
let ABS_ZERO_TAC sname =
  let s = mk_var(sname,`:x86state`) in
  let zth = ASSUME (subst [s,`s:x86state`] `read (memory :> bytes(word_add fb (word 448),800)) s = 0`) in
  let simp = CONV_RULE(DEPTH_CONV NUM_RED_CONV) o REWRITE_RULE[DIV_0; MOD_0] in
  let facts = flat (map (fun (k,b) ->
    let bo = b - 448 in
    map (fun off -> simp(abs_sub_fact KP_RD128 zth (bo + off) 16)) [0;16;32;48] @
    [simp(if k mod 2 = 0 then abs_sub_fact KP_RD128 zth (bo + 64) 16 else abs_sub_fact KP_RD64 zth (bo + 64) 8);
     simp(abs_sub_fact KP_RD8 zth (bo + 66) 1); simp(abs_sub_fact KP_RD8 zth (bo + 135) 1);
     simp(KP_NORM(MP (SPECL [`word_add fb (word 448):int64`; `800`; `0`; mk_small_numeral (bo + 67); `68`; s] READ_MEMORY_BYTES_SUB)
                (CONJ zth (EQT_ELIM(NUM_REDUCE_CONV (mk_binary "<=" (mk_binary "+" (mk_small_numeral (bo+67),`68`),`800`)))))));
     simp(KP_NORM(MP (SPECL [`word_add fb (word 448):int64`; `800`; `0`; mk_small_numeral (bo + 136); `64`; s] READ_MEMORY_BYTES_SUB)
                (CONJ zth (EQT_ELIM(NUM_REDUCE_CONV (mk_binary "<=" (mk_binary "+" (mk_small_numeral (bo+136),`64`),`800`)))))))])
    (zip (0--3) ABS_ST)) in
  MAP_EVERY ASSUME_TAC facts;;

let ABS_ZX_MOD16 = prove(`!y:N word. word (val y MOD 65536):int16 = word_zx y`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; word_zx; VAL_WORD; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL]);;

(* the stored nonce bytes of state k as the subword of word Mk *)
let ABS_FIX16_TAC sname =
  MAP_EVERY (fun (k,b) ->
    let s = mk_var(sname,`:x86state`) in
    let gv = mk_var("g"^string_of_int k,`:int128`) in
    let lt = subst [s,`s:x86state`; mk_small_numeral (b+64),`n:num`] `read (memory :> bytes16 (word_add fb (word n))) s` in
    let gz = mk_comb(`word_zx:int128->int16`,gv) in
    FIRST_X_ASSUM(fun th ->
      let c = concl th in
      if is_eq c && lhs c = lt then
        let eq = prove(mk_eq(rhs c,gz), REWRITE_TAC[ABS_ZX_MOD16] THEN CONV_TAC WORD_BLAST) in
        FIRST_ASSUM(fun gth -> if is_eq(concl gth) && lhs(concl gth) = gz
                               then ASSUME_TAC(TRANS (TRANS th eq) gth) else NO_TAC)
      else NO_TAC)) (zip (0--3) ABS_ST);;

let ABS_FINAL_TAC sname =
  MAP_EVERY (fun k ->
    let mv = mk_var("M"^string_of_int k,`:num`) in
    let bth = ASSUME(subst [mv,`M:num`] `M < 2 EXP 528`) in
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM(MP (SPEC mv ABS_S_WORD) bth)])) (0--3) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let ETA4X_ABS_TAC execth =
  CONCRETIZE_F_EVENTS_TAC `\(fb:int64) (pc:num). f_ev_all fb pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `fb:int64`; `M0:num`; `M1:num`; `M2:num`; `M3:num`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; ALL; NONOVERLAPPING_CLAUSES; fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ABS_ALIGNED_TAC [64;80;96;112;128;160;176;192;208;224;256;272;288;304;320;352;368;384;400;416;
                   448;464;480;496;512;848;864;880;896;912] THEN
  ABS_GHOST_TAC THEN
  MAP_EVERY (fun n -> GHOST_INTRO_TAC (mk_var(Printf.sprintf "ymm%d_init" n,`:int256`))
                       (parse_term(Printf.sprintf "read YMM%d" n))) [0;1;2;3] THEN
  FULL_INIT_TAC THEN
  ABS_INPUT_TAC "s0" THEN ABS_G16_TAC "s0" THEN ABS_ZERO_TAC "s0" THEN
  VERIF_SSE_STEPS_TAC execth (1--75) THEN
  ABS_FIX16_TAC "s75" THEN
  MAP_EVERY (fun (k,b) ->
    ABS_CHAIN_TAC (subst [mk_var("M"^string_of_int k,`:num`),`M:num`] ABS_SW) b "s75")
   (zip (0--3) ABS_ST) THEN
  ABS_FINAL_TAC "s75";;

(* the absorb of function fn (+0x14e to +0x392), with the registers that it
   leaves pointing at the states *)
let PROVE_ABS fn regs =
  let f = layout fn in
  prove(ABS_STMT (f + 0x14e) (f + 0x392) regs,
        ETA4X_ABS_TAC (KPSEED_EXEC (f + 0x14e) (f + 0x392)));;

(* ------------------------------------------------------------------------- *)
(* GUARD: a scan of the outer loop with the test of its flag before it: the  *)
(* flag byte at rsp0 + fo is 1 iff the count offset is below 256; if it is,  *)
(* the scan runs (SCAN), else the code skips it. The first guard of the loop *)
(* also loads the pointers to the polynomials 1 to 3 from their slots on     *)
(* both paths (and to polynomial 0 for its scan).                            *)
(* ------------------------------------------------------------------------- *)

let GUARD_STMT fn start exit eta bo buflen creg preg fo first =
  let pre = if first then
    "read (memory :> bytes64 (word_add rsp0 (word 56))) s = a /\\
               read (memory :> bytes64 (word_add rsp0 (word 32))) s = p1 /\\
               read (memory :> bytes64 (word_add rsp0 (word 40))) s = p2 /\\
               read (memory :> bytes64 (word_add rsp0 (word 48))) s = p3"
    else Printf.sprintf "read %s s = a" preg in
  let post = if first then "read RDI s = p3 /\\ read R8 s = p2 /\\ read R9 s = p1"
    else Printf.sprintf "read %s s = a" preg in
  let vars = if first then " p1 p2 p3" else "" in
  let mch = String.concat "; " (setify (["RIP"; "RAX"; "RCX"; "RDX"; "RSI"; creg] @
              (if first then ["RDI"; "R8"; "R9"; "R10"] else []))) in
  parse_term(subst_tokens
   ["@MC@",image_mc; "@FN@",fn; "@S@",start; "@X@",exit; "@E@",string_of_int eta;
    "@BO@",string_of_int bo; "@BL@",string_of_int buflen; "@C@",creg;
    "@FO@",string_of_int fo; "@PRE@",pre; "@POST@",post; "@V@",vars; "@MCH@",mch]
  "exists f_events.
   forall e a offset b pc rsp0@V@.
     aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
     offset <= 256 /\\
     ALL (nonoverlapping (word_add a (word(4 * offset)),4 * (256 - offset)))
         [(word pc,libmldsa_size); (word_add rsp0 (word @BO@),@BL@);
          (word_add rsp0 (word 28),36)]
     ==> ensures x86
          (\\s. bytes_loaded s (word pc) @MC@ /\\
               read RIP s = word (pc + @FN@_@S@) /\\
               read RSP s = rsp0 /\\
               read (memory :> bytes8 (word_add rsp0 (word @FO@))) s =
               (if offset < 256 then word 1 else word 0) /\\
               @PRE@ /\\
               read @C@ s = word offset /\\
               (!j. j < @BL@ ==> read(memory :> bytes8(word_add rsp0 (word(@BO@ + j)))) s = b j) /\\
               read events s = e)
          (\\s. read RIP s = word (pc + @FN@_@X@) /\\
               read RSP s = rsp0 /\\ @POST@ /\\
               read @C@ s = word(mld_rej_eta_ctr @E@ 256 offset b @BL@) /\\
               (!i. offset <= i /\\ i < mld_rej_eta_ctr @E@ 256 offset b @BL@
                    ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        EL (i - offset) (mld_rej_eta_list @E@ b (2 * @BL@))) /\\
               (exists e2.
                  read events s = APPEND e2 e /\\
                  e2 = f_events a offset rsp0 (mld_rej_eta_declass @E@ 256 offset b @BL@) pc /\\
                  memaccess_inbounds e2
                   [word_add rsp0 (word @BO@),@BL@; word_add rsp0 (word 28),36]
                   [word_add a (word(4 * offset)),4 * (256 - offset)]))
          (MAYCHANGE [@MCH@] ,, MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(word_add a (word(4 * offset)),4 * (256 - offset))])");;

let GUARD_TEMPLATE =
 `\(a:int64) (offset:num) (rsp0:int64) (D:bool list) (pc:num).
   if offset < 256 then f_ev_s a offset rsp0 D pc else f_ev_k a offset rsp0 D pc
   :(uarch_event)list`;;

let GUARD_EXEC fn start exit = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^start), layout (fn^"_"^exit))];;

(* the skipped scan: the count stays at 256 and no coefficient is stored     *)
let GUARD_CTR256 = prove
 (`!eta (b:num->byte) n. mld_rej_eta_ctr eta 256 256 b n = 256`,
  REWRITE_TAC[mld_rej_eta_ctr; SUB_REFL; ARITH_RULE `MIN 0 x = 0`; ADD_CLAUSES]);;

let GUARD_TAC scanth fn start exit eta bo buflen creg preg fo first npre nskip =
  let execth = GUARD_EXEC fn start exit in
  ASSUME_CALLEE_SAFETY_TAILED_TAC scanth "H_SCAN" THEN
  CONCRETIZE_F_EVENTS_TAC GUARD_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC ([`e:(uarch_event)list`; `a:int64`; `offset:num`; `b:num->byte`; `pc:num`; `rsp0:int64`] @
                       (if first then [`p1:int64`; `p2:int64`; `p3:int64`] else [])) THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ABBREV_TAC (mk_eq(`D:bool list`,list_mk_comb(`mld_rej_eta_declass`,
    [mk_small_numeral eta; `256`; `offset:num`; `b:num->byte`; mk_small_numeral buflen]))) THEN
  ASM_CASES_TAC `offset < 256` THEN ASM_REWRITE_TAC[] THENL
   [FULL_INIT_TAC THEN
    X86_STEPS_TAC execth (1--npre) THEN
    REMOVE_THEN "H_SCAN" (fun th ->
      X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
        (mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,execth,0x0,
         mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,th)
        [`e:(uarch_event)list`; `a:int64`; `offset:num`; `b:num->byte`; `pc:num`; `rsp0:int64`] (npre + 1) THENL
       [FULL_EXISTS_E2_TAC (ref [`a:int64`; `offset:num`; `b:num->byte`; `pc:num`; `rsp0:int64`]);
        ALL_TAC]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME(list_mk_comb(`mld_rej_eta_declass`,
      [mk_small_numeral eta; `256`; `offset:num`; `b:num->byte`; mk_small_numeral buflen]) |> fun t -> mk_eq(t,`D:bool list`))]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    SUBGOAL_THEN `offset = 256` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GUARD_CTR256; LT_REFL] THEN
    FULL_INIT_TAC THEN
    X86_STEPS_TAC execth (1--nskip) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `~(256 <= i /\ i < 256)`] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let PROVE_GUARD scanth fn start exit eta bo buflen creg preg fo first npre nskip =
  prove(GUARD_STMT fn start exit eta bo buflen creg preg fo first,
        GUARD_TAC scanth fn start exit eta bo buflen creg preg fo first npre nskip);;

(* ------------------------------------------------------------------------- *)
(* The ABS and GUARD instances: 44 and 87 (eta = 2) have the same code; 65   *)
(* (eta = 4) leaves R12 at the first state before ABS instead of R13, and    *)
(* its outer loop is loop4 to loop7. The scans of the outer loop are the     *)
(* last four of PROVE_ETA2_SCANS and PROVE_ETA4_SCANS.                       *)
(* ------------------------------------------------------------------------- *)

let PROVE_ETA2_ABS fn = PROVE_ABS fn ["R14",648; "R15",848; "R12",1048];;
let PROVE_ETA4_ABS fn = PROVE_ABS fn ["R13",648; "R14",848; "R15",1048];;

let PROVE_ETA2_GUARDS fn scans =
  let sc k = el (4 + k) scans in
  [PROVE_GUARD (sc 0) fn "after_memcpy_8" "join17" 2 0x4e0 136 "R13" "R10" 28 true 8 5;
   PROVE_GUARD (sc 1) fn "join17" "loop6_exit" 2 0x580 136 "RBX" "R9" 29 false 4 2;
   PROVE_GUARD (sc 2) fn "loop6_exit" "loop7_exit" 2 0x620 136 "R14" "R8" 30 false 4 2;
   PROVE_GUARD (sc 3) fn "loop7_exit" "loop8_exit" 2 0x6c0 136 "R15" "RDI" 31 false 4 2];;

let PROVE_ETA4_GUARDS fn scans =
  let sc k = el (4 + k) scans in
  [PROVE_GUARD (sc 0) fn "after_memcpy_12" "join19" 4 0x4e0 136 "R13" "R10" 28 true 8 5;
   PROVE_GUARD (sc 1) fn "join19" "loop5_exit" 4 0x600 136 "RBX" "R9" 29 false 4 2;
   PROVE_GUARD (sc 2) fn "loop5_exit" "loop6_exit" 4 0x720 136 "R14" "R8" 30 false 4 2;
   PROVE_GUARD (sc 3) fn "loop6_exit" "loop7_exit" 4 0x840 136 "R15" "RDI" 31 false 4 2];;
