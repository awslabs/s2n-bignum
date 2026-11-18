(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the constant-time and memory safety proofs of the API           *)
(* functions of the x86 mlkem_native2 (keypair_derand, enc_derand, dec and   *)
(* the internal pke_encrypt and pke_decrypt): the theorems of their callees  *)
(* in the forms the proofs need (the safety of the kernels with the frames   *)
(* of their correctness theorems; mlkem_check_encoding and mlkem_hash_g, on  *)
(* whose results the callers' events depend, as correctness and safety in    *)
(* one, "FULL"), the loops as single steps, and the proof of each function   *)
(* for a parameter set, given the theorems of the callees that depend on     *)
(* it. As arm/proofs/utils/mlkem_native2_kem_safe.ml for AArch64.            *)
(* ========================================================================= *)

needs "x86/proofs/utils/mlkem_native2_kem.ml";;
needs "x86/proofs/utils/mlkem_native2_safety.ml";;
needs "x86/proofs/utils/mlkem_native2_keccak_full.ml";;

(* ------------------------------------------------------------------------- *)
(* The safety of the kernels with the frames of their correctness theorems,  *)
(* as callers need them: for those whose safety theorems are not proved with *)
(* ~keep_maychanges:true, all from the correctness theorems by               *)
(* x86_framed_safe; for the others, the subroutine forms from their core     *)
(* safety theorems, which keep the frames. Those of the kernels that depend  *)
(* on the parameter set are made in the same ways by the proof of each       *)
(* parameter set, for its own.                                               *)
(* ------------------------------------------------------------------------- *)

let x86_framed_of_core_lens lens core0 noibt_correct tmc =
  let conv = REWRITE_CONV lens THENC NUM_REDUCE_CONV THENC
             REWRITE_CONV[ADD_0] in
  let core = if lens = [] then core0 else CONV_RULE conv core0 in
  let noibt = prove(x86_noibt_safe_tm core noibt_correct,
    X86_PROMOTE_RETURN_NOSTACK_TAC tmc core THEN
    DISCHARGE_SAFETY_PROPERTY_TAC) in
  noibt,ADD_IBT_RULE noibt;;

let x86_framed_of_core = x86_framed_of_core_lens [];;

let MLKEM_NTT_CORE_SAFE_FRAMED,MLKEM_NTT_NOIBT_SUBROUTINE_SAFE_FRAMED,
    MLKEM_NTT_SUBROUTINE_SAFE_FRAMED =
  x86_framed_safe "mlkem_ntt_x86" MLKEM_NTT_CORRECT MLKEM_NTT_TMC_EXEC
    MLKEM_NTT_NOIBT_SUBROUTINE_CORRECT mlkem_ntt_tmc;;

let MLKEM_INTT_CORE_SAFE_FRAMED,MLKEM_INTT_NOIBT_SUBROUTINE_SAFE_FRAMED,
    MLKEM_INTT_SUBROUTINE_SAFE_FRAMED =
  x86_framed_safe "mlkem_intt_x86" MLKEM_INTT_CORRECT MLKEM_INTT_TMC_EXEC
    MLKEM_INTT_NOIBT_SUBROUTINE_CORRECT mlkem_intt_tmc;;

let MLKEM_MULCACHE_COMPUTE_CORE_SAFE_FRAMED,
    MLKEM_MULCACHE_COMPUTE_NOIBT_SUBROUTINE_SAFE_FRAMED,
    MLKEM_MULCACHE_COMPUTE_SUBROUTINE_SAFE_FRAMED =
  x86_framed_safe "mlkem_mulcache_compute_x86" MLKEM_MULCACHE_COMPUTE_CORRECT
    MLKEM_MULCACHE_COMPUTE_TMC_EXEC
    MLKEM_MULCACHE_COMPUTE_NOIBT_SUBROUTINE_CORRECT
    mlkem_mulcache_compute_tmc;;

let MLKEM_FROMBYTES_CORE_SAFE_FRAMED,
    MLKEM_FROMBYTES_NOIBT_SUBROUTINE_SAFE_FRAMED,
    MLKEM_FROMBYTES_SUBROUTINE_SAFE_FRAMED =
  x86_framed_safe "mlkem_frombytes" MLKEM_FROMBYTES_CORRECT
    mlkem_frombytes_TMC_EXEC MLKEM_FROMBYTES_NOIBT_SUBROUTINE_CORRECT
    mlkem_frombytes_tmc;;

let MLKEM_TOBYTES_CORE_SAFE_FRAMED,
    MLKEM_TOBYTES_NOIBT_SUBROUTINE_SAFE_FRAMED,
    MLKEM_TOBYTES_SUBROUTINE_SAFE_FRAMED =
  x86_framed_safe "mlkem_tobytes" MLKEM_TOBYTES_CORRECT
    mlkem_tobytes_TMC_EXEC MLKEM_TOBYTES_NOIBT_SUBROUTINE_CORRECT
    mlkem_tobytes_tmc;;

let MLKEM_TOMONT_CORE_SAFE_FRAMED,MLKEM_TOMONT_NOIBT_SUBROUTINE_SAFE_FRAMED,
    MLKEM_TOMONT_SUBROUTINE_SAFE_FRAMED =
  x86_framed_safe "mlkem_tomont" MLKEM_TOMONT_CORRECT mlkem_tomont_TMC_EXEC
    MLKEM_TOMONT_NOIBT_SUBROUTINE_CORRECT mlkem_tomont_tmc;;

let MLKEM_REDUCE_NOIBT_SUBROUTINE_SAFE_FRAMED,
    MLKEM_REDUCE_SUBROUTINE_SAFE_FRAMED =
  x86_framed_of_core MLKEM_REDUCE_SAFE MLKEM_REDUCE_NOIBT_SUBROUTINE_CORRECT
    mlkem_reduce_tmc;;

let MLKEM_ADD_REDUCE_NOIBT_SUBROUTINE_SAFE_FRAMED,
    MLKEM_ADD_REDUCE_SUBROUTINE_SAFE_FRAMED =
  x86_framed_of_core MLKEM_ADD_REDUCE_SAFE
    MLKEM_ADD_REDUCE_NOIBT_SUBROUTINE_CORRECT mlkem_add_reduce_tmc;;

let MLKEM_SUB_REDUCE_NOIBT_SUBROUTINE_SAFE_FRAMED,
    MLKEM_SUB_REDUCE_SUBROUTINE_SAFE_FRAMED =
  x86_framed_of_core MLKEM_SUB_REDUCE_SAFE
    MLKEM_SUB_REDUCE_NOIBT_SUBROUTINE_CORRECT mlkem_sub_reduce_tmc;;

let MLKEM_FROMMSG_NOIBT_SUBROUTINE_SAFE_FRAMED,
    MLKEM_FROMMSG_SUBROUTINE_SAFE_FRAMED =
  x86_framed_of_core MLKEM_FROMMSG_SAFE
    MLKEM_FROMMSG_NOIBT_SUBROUTINE_CORRECT mlkem_frommsg_tmc;;

let MLKEM_TOMSG_NOIBT_SUBROUTINE_SAFE_FRAMED,
    MLKEM_TOMSG_SUBROUTINE_SAFE_FRAMED =
  x86_framed_of_core MLKEM_TOMSG_SAFE
    MLKEM_TOMSG_NOIBT_SUBROUTINE_CORRECT mlkem_tomsg_tmc;;

(* ------------------------------------------------------------------------- *)
(* The zeroing loop of n 128-byte blocks at a (RDI) in the image at lo, from *)
(* the setting of the count (mov ecx, n) to after the loop, with its events. *)
(* ------------------------------------------------------------------------- *)

let api_zero_safe_tm lo n =
  parse_term(Printf.sprintf
   "exists f_events.
     !e a pc. nonoverlapping (a,%d) (word pc,mlkem_native2_image_size)
       ==> ensures x86
            (\\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\\
                 read RIP s = word(pc + %d) /\\ read RDI s = a /\\
                 read events s = e)
            (\\s. read RIP s = word(pc + %d) /\\
                 read RDI s = word_add a (word %d) /\\
                 (exists e2.
                    read events s = APPEND e2 e /\\
                    e2 = f_events a pc /\\
                    memaccess_inbounds e2 [a,%d] [a,%d]))
            (MAYCHANGE [RIP; RDI; RCX] ,, MAYCHANGE SOME_FLAGS ,,
             MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,%d)])"
   (128 * n) (lo - 5) (lo + 30) (128 * n) (128 * n) (128 * n) (128 * n));;

let API_ZERO_SAFE_LOOP exec (lo,n) =
  let cth = api_zero_counter n in
  let nn = mk_small_numeral n in
  let pcp k = mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral k) in
  prove(api_zero_safe_tm lo n,
    REWRITE_TAC[SOME_FLAGS] THEN
    CONCRETIZE_F_EVENTS_TAC
     (vsubst [nn,`n:num`]
       `\(a:int64) (pc:num).
          APPEND (f_ev_epil a pc)
                 (APPEND (ENUMERATEL n (\i. f_ev_loop a pc i))
                         (f_ev_prol a pc)) :(uarch_event)list`) THEN
    REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`a:int64`; `pc:num`] THEN DISCH_TAC THEN
    ENSURES_EVENTS_WHILE_UP2_TAC nn (pcp lo) (pcp (lo + 30))
     (vsubst [nn,`n:num`]
       `\i s. read RDI s = word_add a (word(128 * i)) /\
              read RCX s = word(n - i)`) THEN
    REPEAT CONJ_TAC THENL
     [ARITH_TAC;
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false exec (1--1) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false exec (1--7) THEN
      ASM_SIMP_TAC[cth] THEN
      CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false exec [] THEN
      CONV_TAC NUM_REDUCE_CONV THEN DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The frame of the API functions in the safety proofs. The events depend on *)
(* the frame base, stackpointer + d with d the offset of the alignment       *)
(* (and rsp, -32), so d is given as a function api_ofs of stackpointer: in   *)
(* the simulation as the abbreviation delta (with fb = stackpointer + delta, *)
(* as in the correctness proofs), expanded at the end, where the events must *)
(* be functions of the public variables.                                     *)
(* ------------------------------------------------------------------------- *)

let api_ofs = new_definition
 `api_ofs m (stk:int64) =
    m - val(word_and (word_add stk (word m)) (word 31):int64)`;;

let API_ALIGN_FRAME_OFS = prove
 (`!stk:int64 m.
        31 <= m
        ==> word_and (word_add stk (word m)) (word 18446744073709551584) =
            word_add stk (word(api_ofs m stk)) /\
            api_ofs m stk <= m /\ m <= api_ofs m stk + 31 /\
            aligned 32 (word_add stk (word(api_ofs m stk)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[api_ofs] THEN
  ABBREV_TAC `x:int64 = word_add stk (word m)` THEN
  MP_TAC(ISPECL [`x:int64`; `31`] (CONJUNCT1 VAL_WORD_AND_WORD_LE)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `word_add stk (word(m - val(word_and x (word 31):int64))):int64 =
    word_and x (word 18446744073709551584)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[WORD_SUB; ARITH_RULE `r <= 31 /\ 31 <= m ==> r <= m`] THEN
    REWRITE_TAC[WORD_VAL; WORD_AND_NOT31] THEN EXPAND_TAC "x" THEN
    CONV_TAC WORD_RULE;
    REWRITE_TAC[ALIGNED_WORD_AND_NOT31] THEN ASM_ARITH_TAC]);;

(*** The entry as API_ENTRY_TAC, with e and the offset as api_ofs ***)

let API_SAFE_ENTRY_TAC exec vars n size =
  let m = n - 48 - size in
  let cs = m - 31 in
  let nn = mk_small_numeral n and mm = mk_small_numeral m
  and csn = mk_small_numeral cs and sizen = mk_small_numeral size in
  let fth = CONV_RULE NUM_REDUCE_CONV
   (REWRITE_RULE[IMP_CONJ]
     (SPEC_ALL(SPECL [`stackpointer:int64`; `delta:num`; csn; sizen; nn]
                     API_FRAME_NONOVERLAPPING)))
  and sth = REWRITE_RULE[] (CONV_RULE NUM_REDUCE_CONV
   (REWRITE_RULE[IMP_CONJ]
     (SPECL [`stackpointer:int64`; `delta:num`; csn; sizen; nn]
            API_FRAME_SAVED_NONOVERLAPPING))) in
  let dlo = lhand(concl fth) and dhi = lhand(rand(concl fth)) in
  let stk = mk_pair(`stackpointer:int64`,mk_small_numeral(n + 8)) in
  let frame_fact th =
    let c = concl th in
    let l,r = dest_nonoverlapping c in
    let th' = if l = stk then th
              else if r = stk then ONCE_REWRITE_RULE[NONOVERLAPPING_SYM] th
              else failwith "frame_fact" in
    MATCH_MP (GEN_ALL(MP (MP fth (ASSUME dlo)) (ASSUME dhi))) th' in
  let ofs = mk_comb(mk_comb(`api_ofs`,mm),`stackpointer:int64`) in
  MAP_EVERY X_GEN_TAC vars THEN
  WORD_FORALL_OFFSET_TAC n THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; ALLPAIRS] THEN
  REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  MAP_EVERY (fun r -> ENSURES_PRESERVED_TAC
                (String.lowercase_ascii(fst(dest_const r))^"_init") r)
   [`RBX`; `RBP`; `R12`; `R13`; `R14`; `R15`] THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC exec (1--11) THEN API_RIPREL_TAC THEN
  API_IMAGE_TABLES_TAC 11 THEN
  MP_TAC(SPECL [`stackpointer:int64`; mm] API_ALIGN_FRAME_OFS) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ABBREV_TAC(mk_eq(`delta:num`,ofs)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
                             STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN (mk_conj(dlo,dhi)) STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  (fun (asl,w as gl) ->
     MAP_EVERY (ASSUME_TAC o frame_fact o snd)
       (filter (fun (_,th) -> can frame_fact th) asl) gl) THEN
  ASSUME_TAC(MP (MP sth (ASSUME dlo)) (ASSUME dhi)) THEN
  ABBREV_TAC `fb:int64 = word_add stackpointer (word delta)`;;

(*** At the end: fb and delta expanded in all the assumptions that mention
 *** them, the addresses as stackpointer + offset (with the offsets c of
 *** the callees' stacks below fb, c <= delta), so that the events are
 *** functions of stackpointer and the containments are arithmetic
 ***)

let API_SAFE_EXPAND_TAC (asl,w as gl) =
  let eth = find_asm (fun c ->
    c = `word_add stackpointer (word delta) = fb:int64`) gl in
  let dth = find_asm (fun c -> is_eq c && rand c = `delta:num` &&
                               can (term_match [] `api_ofs m stk`) (lhand c))
              gl in
  let dlo = find_asm (fun c -> is_binary "<=" c && rand c = `delta:num` &&
                               is_numeral(lhand c)) gl in
  let fbsub tm =
    let c = rand(rand tm) in
    let cth = MP (ARITH_RULE(mk_imp(concl dlo,
                mk_binop `(<=):num->num->bool` c `delta:num`))) dlo in
    MP (SPECL [`stackpointer:int64`; `delta:num`; c] API_FB_SUB) cth in
  let pat = `word_sub (word_add stackpointer (word delta)) (word c):int64` in
  let fv = `fb:int64` and dv = `delta:num` in
  let keep th = concl th = concl eth || concl th = concl dth in
  (RULE_ASSUM_TAC(fun th ->
     if keep th || not(free_in fv (concl th) || free_in dv (concl th))
     then th else
     let th1 = REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]
                (REWRITE_RULE[SYM eth]
                  (CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
                    (REWRITE_RULE[WORD_SUB_SUB_NUM] th))) in
     let subs = setify(find_terms (fun t -> can (term_match [] pat) t &&
                                            is_numeral(rand(rand t)))
                         (concl th1)) in
     REWRITE_RULE[SYM dth] (REWRITE_RULE (map fbsub subs) th1)) THEN
   REPEAT(FIRST_X_ASSUM(fun th -> if keep th then ALL_TAC else NO_TAC))) gl;;

(*** The arguments of a framed safety theorem th of the callee name: e,
 *** the C arguments from the registers, the pc, the stack pointer and the
 *** return address
 ***)

let x86_safe_ilist th name =
  let vs = fst(strip_forall(snd(dest_exists(concl th)))) in
  let ca = find_term (fun t ->
    is_comb t && is_comb(rator t) &&
    (try fst(dest_const(rator(rator t))) = "C_ARGUMENTS"
     with Failure _ -> false)) (concl th) in
  let args = dest_list(rand(rator ca)) in
  let regs = ["RDI"; "RSI"; "RDX"; "RCX"; "R8"; "R9"] in
  map (fun v ->
    let n = name_of v in
    if n = "e" then v
    else if n = "pc" then parse_term("pc + "^name)
    else if n = "stackpointer" then `read RSP s`
    else if n = "returnaddress" then `read (memory :> bytes64(read RSP s)) s`
    else parse_term("read "^el (index v args) regs^" s")) vs;;

(*** A safety theorem without its ghost lists, variables v that occur only
 *** in a hypothesis LENGTH v = n (as inlist in those of the compression
 *** functions, which callers cannot give), as REPLICATE n ARB
 ***)

let DROP_GHOST_LISTS_RULE th =
  let f,body = dest_exists(concl th) in
  let vs,imp = strip_forall body in
  let hyp,ens = dest_imp imp in
  let hs = conjuncts hyp in
  let lenth v =
    let cs = filter (free_in v) hs in
    match cs with
      [c] when is_eq c && rand(lhand c) = v &&
               (try fst(dest_const(rator(lhand c))) = "LENGTH"
                with Failure _ -> false) -> rand c
    | _ -> failwith "lenth" in
  let ghosts = filter (fun v -> not(free_in v ens) && can lenth v) vs in
  if ghosts = [] then th else
  let insts = map (fun v ->
    let ety = hd(snd(dest_type(type_of v))) in
    list_mk_icomb "REPLICATE" [lenth v; mk_const("ARB",[ety,aty])],v)
    ghosts in
  let th1 = INST insts (SPECL vs (ASSUME body)) in
  let th2 = PURE_REWRITE_RULE[LENGTH_REPLICATE; AND_CLAUSES] th1 in
  let th3 = GENL (subtract vs ghosts) th2 in
  CHOOSE (f,th) (EXISTS (mk_exists(f,concl th3),f) th3);;

(*** tobytes with the frame of MLKEM_TOBYTES_NOIBT_SUBROUTINE_CORRECT_384,
 *** whose output region is the 384 bytes written (in the library theorem
 *** it is 512 bytes for its nonoverlapping with the return address)
 ***)

let MLKEM_TOBYTES_NOIBT_SUBROUTINE_SAFE_FRAMED_384,
    MLKEM_TOBYTES_SUBROUTINE_SAFE_FRAMED_384 =
  x86_framed_of_core MLKEM_TOBYTES_CORE_SAFE_FRAMED
    MLKEM_TOBYTES_NOIBT_SUBROUTINE_CORRECT_384 mlkem_tobytes_tmc;;

(*** The framed safety theorems of the kernels, with their labels, to which
 *** the proof of a parameter set adds those of its own kernels
 ***)

let api_safe_kernels = ref
  ["mlkem_frombytes","H_FROMBYTES",MLKEM_FROMBYTES_SUBROUTINE_SAFE_FRAMED,
   mlkem_frombytes_mc;
   "mlkem_tobytes","H_TOBYTES",MLKEM_TOBYTES_SUBROUTINE_SAFE_FRAMED_384,
   mlkem_tobytes_mc;
   "mlkem_frommsg","H_FROMMSG",MLKEM_FROMMSG_SUBROUTINE_SAFE_FRAMED,
   mlkem_frommsg_mc;
   "mlkem_tomsg","H_TOMSG",MLKEM_TOMSG_SUBROUTINE_SAFE_FRAMED,
   mlkem_tomsg_mc;
   "mlkem_ntt_x86","H_NTT",MLKEM_NTT_SUBROUTINE_SAFE_FRAMED,mlkem_ntt_mc;
   "mlkem_intt_x86","H_INTT",MLKEM_INTT_SUBROUTINE_SAFE_FRAMED,mlkem_intt_mc;
   "mlkem_mulcache_compute_x86","H_MULCACHE",
   MLKEM_MULCACHE_COMPUTE_SUBROUTINE_SAFE_FRAMED,mlkem_mulcache_compute_mc;
   "mlkem_tomont","H_TOMONT",MLKEM_TOMONT_SUBROUTINE_SAFE_FRAMED,
   mlkem_tomont_mc;
   "mlkem_reduce","H_REDUCE",MLKEM_REDUCE_SUBROUTINE_SAFE_FRAMED,
   mlkem_reduce_mc;
   "mlkem_add_reduce","H_ADD",MLKEM_ADD_REDUCE_SUBROUTINE_SAFE_FRAMED,
   mlkem_add_reduce_mc;
   "mlkem_sub_reduce","H_SUB",MLKEM_SUB_REDUCE_SUBROUTINE_SAFE_FRAMED,
   mlkem_sub_reduce_mc];;

let api_add_safe_kernels l = api_safe_kernels := !api_safe_kernels @ l;;

(*** The assumptions of the safety theorems of the kernels names and of the
 *** lemmas lems (label, theorem), and the calls of them for the run driver
 *** (with the stack pointer after the return simplified), the events a
 *** function of vars
 ***)

let API_SAFE_ASSUME_TAC names lems =
  let ks = filter (fun (n,_,_,_) -> mem n names) !api_safe_kernels in
  MAP_EVERY (fun (_,label,th,_) ->
    ASSUME_CALLEE_TAILED_TAC (DROP_GHOST_LISTS_RULE th) label) ks THEN
  MAP_EVERY (fun (label,th) -> ASSUME_CALLEE_TAILED_TAC th label) lems;;

(*** Before a call at state k: the image addresses in the argument
 *** registers as word(pc + n), and the alignment of the buffers
 ***)

let API_SAFE_PRE_TAC k =
  MAP_EVERY (fun r -> TRY(API_REG_PCADD_TAC r k))
   [`RDI`; `RSI`; `RDX`; `RCX`; `R8`; `R9`] THEN
  API_ALIGNED_TAC k;;

let api_safe_calls exec vars names lems =
  let ks = filter (fun (n,_,_,_) -> mem n names) !api_safe_kernels in
  map (fun (name,label,th,mc) ->
         layout name,
         (fun k -> API_SAFE_PRE_TAC k THEN
                   NATIVE2_SAFE_THM_TAC exec vars label (layout name,mc) I
                    (x86_safe_ilist (DROP_GHOST_LISTS_RULE th) name) k THEN
                   API_RSP_TAC)) ks @
  map (fun (off,label,ilist) ->
         off,
         NATIVE2_SAFE_THM_TAC exec vars label (0,mlkem_native2_image_mc) I
           ilist) lems;;

(*** The addresses in the events of the definitions of NATIVE2_SAFE_RUN_TAC,
 *** expanded at the end, which were in terms of fb, normalized as
 *** API_SAFE_EXPAND_TAC normalizes those of the facts: stackpointer plus or
 *** minus an offset from api_ofs, as the facts of the calls have them
 ***)

let API_SAFE_GOAL_EXPAND_TAC =
  let pat = `word_sub (word_add stackpointer (word d)) (word c):int64` in
  REWRITE_TAC[WORD_SUB_SUB_NUM] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  (fun (asl,w as gl) ->
     let subs = setify(find_terms (fun t -> can (term_match [] pat) t &&
                                            is_numeral(rand(rand t))) w) in
     let fbsub t =
       let d = rand(rand(lhand t)) and c = rand(rand t) in
       let lo = find_asm (fun a -> is_binary "<=" a && rand a = d &&
                                   is_numeral(lhand a)) gl in
       let cth = MP (ARITH_RULE(mk_imp(concl lo,
                   mk_binop `(<=):num->num->bool` c d))) lo in
       MP (SPECL [`stackpointer:int64`; d; c] API_FB_SUB) cth in
     REWRITE_TAC (mapfilter fbsub subs) gl);;

let API_SAFE_FINAL_TAC =
  API_EXPAND_FB_TAC THEN API_SAFE_EXPAND_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MEMACCESS_NUMERALS_TAC THEN
  NATIVE2_DISCHARGE_FRESH_NORM_TAC API_SAFE_GOAL_EXPAND_TAC;;

(* ------------------------------------------------------------------------- *)
(* pke_decrypt.                                                              *)
(* ------------------------------------------------------------------------- *)

let pd_safe_parts k ex =
  let nm = api_param k in
  let names = ["mlkem_decompress_d"^string_of_int(api_du k)^"_x86";
               "mlkem_decompress_d"^string_of_int(api_dv k)^"_x86";
               "mlkem_frombytes"; "mlkem_ntt_x86";
               "mlkem_mulcache_compute_x86";
               "mlkem_basemul_k"^string_of_int k; "mlkem_intt_x86";
               "mlkem_sub_reduce"; "mlkem_tomsg"] in
  let zs = api_zero_loops (nm ^ "_pke_decrypt") in
  let zths = map (API_ZERO_SAFE_LOOP ex) zs in
  let zlabels = map (fun i -> "H_Z"^string_of_int i) (0--(length zs - 1)) in
  let vars = [`mp:int64`; `ct:int64`; `sk:int64`; `pc:num`;
              `stackpointer:int64`; `returnaddress:int64`;
              `fb:int64`; `delta:num`] in
  let zil = [`e:(uarch_event)list`; `read RDI s`; `pc:num`] in
  let calls = api_safe_calls ex vars names
                (map2 (fun (lo,_) l -> lo - 5,l,zil) zs zlabels) in
  let setup =
    API_SAFE_ASSUME_TAC names (zip zlabels zths) THEN
    META_EXISTS_TAC THEN
    API_SAFE_ENTRY_TAC ex
     [`e:(uarch_event)list`; `mp:int64`; `ct:int64`; `sk:int64`; `pc:num`]
     (pd_stack k) (pd_frame k) in
  setup,calls;;

let MLKEM_NATIVE2_PKE_DECRYPT_SAFE_TAC k ex =
  let setup,calls = pd_safe_parts k ex in
  setup THEN NATIVE2_SAFE_RUN_TAC ex [] calls 11 THEN API_SAFE_FINAL_TAC;;

(* ------------------------------------------------------------------------- *)
(* pke_encrypt.                                                              *)
(* ------------------------------------------------------------------------- *)

let pe_safe_parts k ex =
  let nm = api_param k in
  let names = ["mlkem_frommsg"; "mlkem_frombytes"; "mlkem_ntt_x86";
               "mlkem_mulcache_compute_x86";
               "mlkem_basemul_k"^string_of_int k; "mlkem_intt_x86";
               "mlkem_add_reduce";
               "mlkem_compress_d"^string_of_int(api_du k)^"_x86";
               "mlkem_compress_d"^string_of_int(api_dv k)^"_x86"] in
  let zs = api_zero_loops (nm ^ "_pke_encrypt") in
  let zths = map (API_ZERO_SAFE_LOOP ex) zs in
  let zlabels = map (fun i -> "H_Z"^string_of_int i) (0--(length zs - 1)) in
  let vars = [`ct:int64`; `at:int64`; `pk:int64`; `mp:int64`;
              `noise:int64`; `pc:num`; `stackpointer:int64`;
              `returnaddress:int64`; `fb:int64`; `delta:num`] in
  let zil = [`e:(uarch_event)list`; `read RDI s`; `pc:num`] in
  let calls = api_safe_calls ex vars names
                (map2 (fun (lo,_) l -> lo - 5,l,zil) zs zlabels) in
  let setup =
    API_SAFE_ASSUME_TAC names (zip zlabels zths) THEN
    META_EXISTS_TAC THEN
    API_SAFE_ENTRY_TAC ex
     [`e:(uarch_event)list`; `ct:int64`; `at:int64`; `pk:int64`;
      `mp:int64`; `noise:int64`; `pc:num`]
     (pe_stack k) (pe_frame k) in
  setup,calls;;

let MLKEM_NATIVE2_PKE_ENCRYPT_SAFE_TAC k ex =
  let setup,calls = pe_safe_parts k ex in
  setup THEN NATIVE2_SAFE_RUN_TAC ex [] calls 11 THEN API_SAFE_FINAL_TAC;;

(* ------------------------------------------------------------------------- *)
(* The modulus check mlkem_check_encoding as correctness and safety in one   *)
(* ("FULL"): the result of MLKEM_CHECK_ENCODING_CORRECT and the events of    *)
(* MLKEM_CHECK_ENCODING_SAFE (which do not depend on the data), for          *)
(* enc_derand, whose events depend on the result. The loop as in the latter, *)
(* with the branch back in the body.                                         *)
(* ------------------------------------------------------------------------- *)

let check_encoding_full_tm =
 `exists f_events.
    forall e a k n pc.
        ensures x86
        (\s. bytes_loaded s (word pc) (BUTLAST mlkem_check_encoding_tmc) /\
             read RIP s = word pc /\
             C_ARGUMENTS [a; k] s /\
             read (memory :> bytes(a,384 * val k)) s = n /\
             read events s = e)
        (\s. read RIP s = word (pc + 0x348) /\
             C_RETURN s =
             (if !i. i < 256 * val k
                     ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329
              then word 1 else word 0) /\
             (exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_events a k pc /\
                  memaccess_inbounds e2 [a,(384 * val k) * 1] []))
        (MAYCHANGE [RIP; RAX; RDI; RSI] ,,
         MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
                    ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
         MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`;;

let CHECK_ENCODING_FULL_SETUP_TAC =
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (k:int64) (pc:num).
      if val k = 0 then f_ev_zero a k pc
      else APPEND (f_ev_epil a k pc)
                  (APPEND (ENUMERATEL (val k) (\i. f_ev_loop a k pc i))
                          (f_ev_prol a k pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `a:int64` THEN W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS;
              fst MLKEM_CHECK_ENCODING_TMC_EXEC] THEN
  ASM_REWRITE_TAC[];;

let CHECK_ENCODING_FULL_ZERO_TAC =
  ASM_REWRITE_TAC[MULT_CLAUSES; LT] THEN ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_CHECK_ENCODING_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[]) (1--22) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(CONJ_TAC THENL [CONV_TAC WORD_REDUCE_CONV THEN NO_TAC; ALL_TAC]) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let check_encoding_full_inv =
  `\i s. read RDI s = word_add a (word(384 * i)) /\
         read RSI s = word(k - i) /\
         read YMM0 s =
         word_join (word 0x0d000d000d000d000d000d000d000d00:int128)
                   (word 0x0d000d000d000d000d000d000d000d00:int128) /\
         read YMM5 s =
         word_join (word 0x0fff0fff0fff0fff0fff0fff0fff0fff:int128)
                   (word 0x0fff0fff0fff0fff0fff0fff0fff0fff:int128) /\
         read YMM6 s =
         word_join (word 0x0f0e0e0d0c0b0b0a0908080706050504:int128)
                   (word 0x0b0a0a09080707060504040302010100:int128) /\
         read (memory :> bytes(a,384 * k)) s = n /\
         !j. j < 16
             ==> word_subword (read YMM4 s) (16 * j,16):int16 =
                 if ?t. t < 16 * i /\ cenc_bad n (16 * t + j)
                 then word 65535 else word 0`;;

let CHECK_ENCODING_FULL_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `word_sub (word (k - i)) (word 1):int64 = word(k - (i + 1)) /\
    val(word(k - (i + 1)):int64) = k - (i + 1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `k - (i + 1) = k - i - 1`] THEN
      GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < k ==> 1 <= k - i`];
      REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      UNDISCH_TAC `k < 2 EXP 64` THEN ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC
   `c:3072 word = word((n DIV 2 EXP (8 * (384 * i))) MOD 2 EXP 3072)` THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ABBREV_TAC `acc = read YMM4 s0` THEN
  MP_TAC(SPECL [`a:int64`; `384 * k`; `n:num`; `384 * i`; `s0:x86state`]
    CHECK_ENCODING_LOADS) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [UNDISCH_TAC `i < k` THEN ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  MAP_EVERY (fun m ->
    ABBREV_TAC(mk_eq(mk_var("l"^string_of_int m,`:int128`),
                     mk_wsubword `c:3072 word`
                       (192 * (m / 2) + 64 * (m mod 2)) 128)))
   (0--31) THEN
  STRIP_TAC THEN
  MAP_EVERY (fun k ->
    X86_STEPS_TAC MLKEM_CHECK_ENCODING_TMC_EXEC [k] THEN
    SIMD_SIMPLIFY_TAC[] THEN
    (if k <= 128 && k mod 8 = 7 then
       let blk = k / 8 in
       CHUNK_ABSTRACT_TAC CHECK_ENCODING_CHUNK
         (if blk mod 2 = 0 then `YMM1` else `YMM3`)
         [mk_var("l"^string_of_int(2 * blk),`:int128`);
          mk_var("l"^string_of_int(2 * blk + 1),`:int128`)] k
     else ALL_TAC)) (1--131) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EVENTS_SPLIT_TAC
   (CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    MP_TAC(SPECL [`n:num`; `i:num`; `c:3072 word`] CHECK_ENCODING_FIELD) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
    STRIP_TAC THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[WORD_SUBWORD_OR] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o
      check (fun th -> free_in `acc:int256` (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[EXISTS_LT_ADD16] THEN
    REWRITE_TAC[ARITH_RULE `16 * (16 * i + m) + j = 256 * i + 16 * m + j`;
                ARITH_RULE `16 * (16 * i) + j = 256 * i + j`] THEN
    MAP_EVERY (fun m ->
      let v = mk_var("l"^string_of_int m,`:int128`) in
      FIRST_ASSUM(fun th ->
        let c = concl th in
        if is_eq c && rhs c = v && is_comb(lhs c) &&
           fst(strip_comb(lhs c)) = `word_subword:3072 word->num#num->int128`
        then SUBST1_TAC(SYM th) else NO_TAC)) (0--31) THEN
    UNDISCH_TAC `j < 16` THEN SPEC_TAC(`j:num`,`j:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[CHECK_ENCODING_OR_MASK; GSYM DISJ_ASSOC]);;

let MLKEM_CHECK_ENCODING_FULL = time prove
 (check_encoding_full_tm,
  CHECK_ENCODING_FULL_SETUP_TAC THEN
  ASM_CASES_TAC `k = 0` THENL [CHECK_ENCODING_FULL_ZERO_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `k:num` `pc + 0x6d` `pc + 0x33b`
    check_encoding_full_inv THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_JOIN_CONV) THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** The initialization, with all lanes 0 ***)

    ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_CHECK_ENCODING_TMC_EXEC [n] THEN
                        SIMD_SIMPLIFY_TAC[]) (1--18) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    EVENTS_SPLIT_TAC
     (REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0; LT; WORD_SUBWORD_0;
                  EXISTS_SIMP]);

    (*** The loop body with the branch back ***)

    CHECK_ENCODING_FULL_BODY_TAC;

    (*** The test of the accumulator ***)

    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ABBREV_TAC `acc = read YMM4 s0` THEN
    MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_CHECK_ENCODING_TMC_EXEC [n] THEN
                        SIMD_SIMPLIFY_TAC[]) (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    EVENTS_SPLIT_TAC
     (REWRITE_TAC[VAL_EQ_0; CHECK_ENCODING_ALL; CHECK_ENCODING_ZERO] THEN
      ASM_SIMP_TAC[CHECK_ENCODING_MASK_ZERO] THEN
      COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV)]);;

(*** The subroutine forms, with the frame of the correctness theorem ***)

let MLKEM_CHECK_ENCODING_NOIBT_SUBROUTINE_FULL = time prove
 (`exists f_events.
    forall e a k n pc stackpointer returnaddress.
        ensures x86
        (\s. bytes_loaded s (word pc) mlkem_check_encoding_tmc /\
             read RIP s = word pc /\
             read RSP s = stackpointer /\
             read (memory :> bytes64 stackpointer) s = returnaddress /\
             C_ARGUMENTS [a; k] s /\
             read (memory :> bytes(a,384 * val k)) s = n /\
             read events s = e)
        (\s. read RIP s = returnaddress /\
             read RSP s = word_add stackpointer (word 8) /\
             C_RETURN s =
             (if !i. i < 256 * val k
                     ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329
              then word 1 else word 0) /\
             (exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_events a k pc stackpointer returnaddress /\
                  memaccess_inbounds e2
                    [a,(384 * val k) * 1; stackpointer,8]
                    [stackpointer,8]))
        (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_check_encoding_tmc
    MLKEM_CHECK_ENCODING_FULL THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_CHECK_ENCODING_SUBROUTINE_FULL =
  ADD_IBT_RULE MLKEM_CHECK_ENCODING_NOIBT_SUBROUTINE_FULL;;

(* ------------------------------------------------------------------------- *)
(* The hash G (mlkem_hash_g) as correctness and safety in one for messages   *)
(* of one block (less than 72 bytes, e.g. the 33 bytes d || k of key         *)
(* generation): the whole words and the single bytes of the block, the       *)
(* padding and the permutation in FULL form, as the lemmas of its            *)
(* correctness proof. As for AArch64.                                        *)
(* ------------------------------------------------------------------------- *)

(*** The decrement of a loop counter and the test after it, with the
 *** bound of n by bnd
 ***)

let HG_COUNTER_TAC =
  let pth = prove
   (`!n k. k < n /\ n < 2 EXP 64
           ==> word_sub (word(n - k)) (word 1):int64 = word(n - (k + 1)) /\
               (~(val(word(n - (k + 1)):int64) = 0) <=> k + 1 < n)`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN `n - k = (n - (k + 1)) + 1` SUBST1_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE];
      SUBGOAL_THEN `val(word(n - (k + 1)):int64) = n - (k + 1)`
      SUBST1_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        ASM_ARITH_TAC;
        ASM_ARITH_TAC]]) in
  fun n k bnd ->
    MP_TAC(SPECL [n; k] pth) THEN
    ANTS_TAC THENL [CONJ_TAC THENL [ASM_REWRITE_TAC[]; bnd]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC);;

let MLKEM_HASH_G_WORDS_FULL = prove
 (full_step_tm_of (concl MLKEM_HASH_G_WORDS)
   [`inp:int64`; `q:num`; `t:num`; `stackpointer:int64`; `pc:num`]
   [`inp:int64,LENGTH(m:byte list)`; `stackpointer:int64,200`]
   [`stackpointer:int64,200`],
  CONCRETIZE_F_EVENTS_TAC
   `\(inp:int64) (q:num) (t:num) (stackpointer:int64) (pc:num).
      if t DIV 8 = 0 then f_ev_skip inp q t stackpointer pc
      else APPEND (f_ev_exit inp q t stackpointer pc)
             (APPEND (ENUMERATEL (t DIV 8)
                       (\k. f_ev_word inp q t stackpointer pc k))
                     (f_ev_entry inp q t stackpointer pc))
      :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o
    check (fun th -> concl th = `LENGTH(m:byte list) = 72 * q + t`)) THEN
  SUBGOAL_THEN `t < 2 EXP 64` ASSUME_TAC THENL
   [UNDISCH_TAC `t < 72` THEN ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `t:num` THEN
  SUBGOAL_THEN `word_ushr (word t:int64) 3 = word(t DIV 8)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `t < 72` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `t DIV 8 < 9` ASSUME_TAC THENL
   [UNDISCH_TAC `t < 72` THEN ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `t DIV 8` THEN
  SUBGOAL_THEN `val(word t:int64) < 72` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `t DIV 8 = 0` THEN ASM_REWRITE_TAC[] THENL
   [ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC MLKEM_HASH_G_EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; EXP; MOD_1; WORD_XOR_0;
                    WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `t DIV 8` `pc + mlkem_hash_g_lastwords`
   `pc + mlkem_hash_g_lastbytes`
   `\k s. read RSP s = stackpointer /\
          read RDI s = word_add stackpointer (word(8 * k)) /\
          read RCX s = word(t DIV 8 - k) /\
          read RBP s = word_add inp (word(72 * q + 8 * k)) /\
          read R12 s = word t /\
          read R13 s = c /\
          read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
          read (memory :> bytes(c,192)) s =
          num_of_wordlist round_constants /\
          read (memory :> wbytes stackpointer) s =
          word_xor (A:1600 word)
           (word((num_of_bytelist m DIV 2 EXP (8 * 72 * q)) MOD
                 2 EXP (64 * k)))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** The entry, past the test for no whole words ***)

    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC MLKEM_HASH_G_EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; EXP; MOD_1; WORD_XOR_0;
                    WORD_ADD_0; SUB_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, for word and lane k ***)

    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `k < 25 /\ (72 * q + 8 * k) + 8 <= LENGTH(m:byte list)`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`k < t DIV 8`; `t < 72`;
                             `72 * q + t = LENGTH(m:byte list)`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] o
      REWRITE_RULE[READ_MEMORY_WBYTES_LANES] o
      check (can (term_match []
        `read (memory :> wbytes a) s = (x:1600 word)`) o concl)) THEN
    DISCH_THEN(fun th ->
      ASSUME_TAC(MP (SPEC `k:num` th) (ASSUME `k < 25`)) THEN
      ASSUME_TAC(RESTRICT_RULE `k:num` th)) THEN
    MP_TAC(SPECL [`inp:int64`; `LENGTH(m:byte list)`; `num_of_bytelist m`;
                  `72 * q + 8 * k`; `s0:x86state`]
      READ_MEMORY_BYTES64_OF_NUM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    X86_STEPS_TAC MLKEM_HASH_G_EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    HG_COUNTER_TAC `t DIV 8` `k:num`
     (UNDISCH_TAC `t DIV 8 < 9` THEN ARITH_TAC) THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [COND_CASES_TAC THEN REWRITE_TAC[];
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
      REWRITE_TAC[READ_MEMORY_WBYTES_LANES] THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      ASM_SIMP_TAC[LANE_XOR_STEP] THEN COND_CASES_TAC THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE
          `8 * 72 * q + 64 * k = 8 * (72 * q + 8 * k)`];
        ASM_SIMP_TAC[]];
      DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The exit to the single bytes ***)

    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let MLKEM_HASH_G_BYTES_FULL = prove
 (full_step_tm_of (concl MLKEM_HASH_G_BYTES)
   [`inp:int64`; `q:num`; `t:num`; `stackpointer:int64`; `pc:num`]
   [`inp:int64,LENGTH(m:byte list)`; `stackpointer:int64,200`]
   [`stackpointer:int64,200`],
  CONCRETIZE_F_EVENTS_TAC
   `\(inp:int64) (q:num) (t:num) (stackpointer:int64) (pc:num).
      if t MOD 8 = 0 then f_ev_skip inp q t stackpointer pc
      else APPEND (f_ev_exit inp q t stackpointer pc)
             (APPEND (ENUMERATEL (t MOD 8)
                       (\k. f_ev_byte inp q t stackpointer pc k))
                     (f_ev_entry inp q t stackpointer pc))
      :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o
    check (fun th -> concl th = `LENGTH(m:byte list) = 72 * q + t`)) THEN
  SUBGOAL_THEN `t < 2 EXP 64` ASSUME_TAC THENL
   [UNDISCH_TAC `t < 72` THEN ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `t:num` THEN
  SUBGOAL_THEN `t MOD 8 < 8` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `t MOD 8` THEN
  MP_TAC(SPEC `t:num` WORD_AND_7_ZX32) THEN
  ANTS_TAC THENL [UNDISCH_TAC `t < 72` THEN ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `num_of_bytelist m DIV 2 EXP (8 * 72 * q) < 2 EXP (8 * t)`
  ASSUME_TAC THENL
   [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB; GSYM MULT_ASSOC] THEN
    ASM_REWRITE_TAC[GSYM EXP_EXP] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_EXP_CONV) THEN
    REWRITE_TAC[NUM_OF_BYTELIST_BOUND];
    ALL_TAC] THEN
  ASM_CASES_TAC `t MOD 8 = 0` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `8 * t DIV 8 = t` ASSUME_TAC THENL
     [MP_TAC(SPECL [`t:num`; `8`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC MLKEM_HASH_G_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ARITH_RULE `64 * t DIV 8 = 8 * (8 * t DIV 8)`] THEN
    REPEAT CONJ_TAC THEN TRY(ASM_SIMP_TAC[MOD_LT] THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `t MOD 8` `pc + mlkem_hash_g_lastbyte`
   `pc + mlkem_hash_g_pad`
   `\k s. read RSP s = stackpointer /\
          read RDI s = word_add stackpointer (word(8 * t DIV 8 + k)) /\
          read RCX s = word(t MOD 8 - k) /\
          read RBP s = word_add inp (word(72 * q + 8 * t DIV 8 + k)) /\
          read R12 s = word t /\
          read R13 s = c /\
          read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
          read (memory :> bytes(c,192)) s =
          num_of_wordlist round_constants /\
          read (memory :> wbytes stackpointer) s =
          word_xor (A:1600 word)
           (word((num_of_bytelist m DIV 2 EXP (8 * 72 * q)) MOD
                 2 EXP (8 * (8 * t DIV 8 + k))))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** The entry, past the test for no single bytes ***)

    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC MLKEM_HASH_G_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; SUB_0;
                    ARITH_RULE `8 * 8 * t DIV 8 = 64 * t DIV 8`] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, for byte 8 * t DIV 8 + k ***)

    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `8 * t DIV 8 + k < 200 /\
      72 * q + 8 * t DIV 8 + k < LENGTH(m:byte list)`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`k < t MOD 8`; `t < 72`;
                             `72 * q + t = LENGTH(m:byte list)`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] o
      REWRITE_RULE[READ_MEMORY_WBYTES_BYTES] o
      check (can (term_match []
        `read (memory :> wbytes a) s = (x:1600 word)`) o concl)) THEN
    DISCH_THEN(fun th ->
      ASSUME_TAC(MP (SPEC `8 * t DIV 8 + k` th)
                    (ASSUME `8 * t DIV 8 + k < 200`)) THEN
      ASSUME_TAC(RESTRICT_RULE `8 * t DIV 8 + k` th)) THEN
    MP_TAC(SPECL [`inp:int64`; `LENGTH(m:byte list)`; `num_of_bytelist m`;
                  `72 * q + 8 * t DIV 8 + k`; `s0:x86state`]
      READ_MEMORY_BYTES8_OF_NUM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    X86_STEPS_TAC MLKEM_HASH_G_EXEC (1--6) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BYTE_ZX_X86]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    HG_COUNTER_TAC `t MOD 8` `k:num` ARITH_TAC THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [COND_CASES_TAC THEN REWRITE_TAC[];
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
      REWRITE_TAC[READ_MEMORY_WBYTES_BYTES] THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      REWRITE_TAC[ARITH_RULE
       `8 * t DIV 8 + k + 1 = (8 * t DIV 8 + k) + 1`] THEN
      ASM_SIMP_TAC[BYTE_XOR_STEP] THEN COND_CASES_TAC THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2 EXP 8 = 256`;
                    ARITH_RULE `8 * 72 * q + 8 * (8 * t DIV 8 + k) =
                                8 * (72 * q + 8 * t DIV 8 + k)`];
        ASM_SIMP_TAC[]];
      DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The exit to the padding ***)

    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `8 * t DIV 8 + t MOD 8 = t` SUBST1_TAC THENL
     [MP_TAC(SPECL [`t:num`; `8`] DIVISION) THEN ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY(ASM_SIMP_TAC[MOD_LT] THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let MLKEM_HASH_G_PAD_FULL = prove
 (full_step_tm_of (concl MLKEM_HASH_G_PAD)
   [`t:num`; `c:int64`; `stackpointer:int64`; `pc:num`]
   [`stackpointer:int64,200`; `c:int64,192`;
    `word(pc + sha3_keccak_f1600_alt2_rotations):int64,384`;
    `word_sub stackpointer (word 8):int64,8`]
   [`stackpointer:int64,200`; `word_sub stackpointer (word 8):int64,8`],
  ASSUME_CALLEE_TAILED_TAC SHA3_KECCAK_F1600_ALT2_IMAGE_FULL_F1600 "H_K1" THEN
  META_EXISTS_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** The domain byte at byte t ***)

  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] o
    REWRITE_RULE[READ_MEMORY_WBYTES_BYTES] o
    check (can (term_match [] `read (memory :> wbytes a) s = (x:1600 word)`) o
           concl)) THEN
  DISCH_THEN(fun th ->
    ASSUME_TAC(MP (SPEC `t:num` th)
                  (MP (ARITH_RULE `t < 72 ==> t < 200`)
                      (ASSUME `t < 72`))) THEN
    ASSUME_TAC(RESTRICT_RULE `t:num` th)) THEN
  X86_STEPS_TAC MLKEM_HASH_G_EXEC [1] THEN
  SUBGOAL_THEN
   `!j. j < 200
        ==> read (memory :> bytes8 (word_add stackpointer (word j))) s1 =
            word_subword (word_xor (A:1600 word) (word(2 EXP (8 * t) * 6)))
                         (8 * j,8)`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[BYTE_XOR_SHIFT; ARITH_RULE `6 < 256`;
                 ARITH_RULE `t < 72 ==> t < 200`] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN

  (*** The final bit at byte 71 ***)

  DISCH_THEN(fun th ->
    ASSUME_TAC(CONV_RULE NUM_REDUCE_CONV
      (MP (SPEC `71` th) (ARITH_RULE `71 < 200`))) THEN
    ASSUME_TAC(RESTRICT_RULE `71` th)) THEN
  X86_STEPS_TAC MLKEM_HASH_G_EXEC (2--5) THEN
  SUBGOAL_THEN
   `read (memory :> wbytes stackpointer) s5 =
    word_xor (word_xor (A:1600 word) (word(2 EXP (8 * t) * 6)))
             (word(2 EXP (8 * 71) * 128))`
  ASSUME_TAC THENL
   [REWRITE_TAC[READ_MEMORY_WBYTES_BYTES] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[BYTE_XOR_SHIFT; ARITH_RULE `128 < 256 /\ 71 < 200`] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN

  (*** The permutation ***)

  SUBGOAL_THEN `wordlist_from_memory(c,24) s5 = round_constants`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[WORDLIST_FROM_MEMORY_ROUND_CONSTANTS]; ALL_TAC] THEN
  REMOVE_THEN "H_K1" (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
     (mlkem_native2_image_mc,MLKEM_HASH_G_EXEC,0,mlkem_native2_image_mc,
      FRESH_TAIL_RULE th)
     [`e:(uarch_event)list`; `read RDI s`; `read RSI s`;
      `word_xor (word_xor (A:1600 word) (word(2 EXP (8 * t) * 6)))
                (word(2 EXP (8 * 71) * 128))`;
      `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`] 6
    THENL
     [EXISTS_E2_TAC (ref [`t:num`; `c:int64`; `stackpointer:int64`;
                          `pc:num`]);
      LABEL_TAC "H_K1" th]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_add (word_sub x (word 8)) (word 8):int64 = x`]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let hg_vars = [`inp:int64`; `len:num`; `c:int64`; `out:int64`; `pc:num`;
               `stackpointer:int64`; `returnaddress:int64`];;

let HG_LEMMA_CALL_TAC label args n =
  REMOVE_THEN label (fun th ->
    let th' = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
               (REWRITE_RULE[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0; EXP;
                             DIV_1]
                 (SPECL (`e:(uarch_event)list` :: args) th)) in
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
     (mlkem_native2_image_mc,MLKEM_HASH_G_EXEC,0,mlkem_native2_image_mc,
      FRESH_TAIL_RULE th') [] n THENL
     [EXISTS_E2_TAC (ref hg_vars); LABEL_TAC label th]);;

let MLKEM_HASH_G_SHORT_SUBROUTINE_FULL = time prove
 (`exists f_events.
     forall e out inp (m:byte list) len c pc stackpointer returnaddress.
       LENGTH m = len /\ len < 72 /\
       ALL (nonoverlapping (word_sub stackpointer (word 256),256))
           [(word pc,mlkem_native2_image_size); (inp,len); (c,192)] /\
       ALL (nonoverlapping (out,64))
           [(word pc,mlkem_native2_image_size);
            (word_sub stackpointer (word 256),264)]
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read RIP s = word(pc + mlkem_hash_g) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [out; inp; word len; c] s /\
                 read (memory :> bytes(inp,len)) s = num_of_bytelist m /\
                 wordlist_from_memory(c,24) s = round_constants /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 read (memory :> bytes(out,64)) s =
                 num_of_bytelist(sha3_512 m) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events inp len c out pc
                           (word_sub stackpointer (word 256)) returnaddress /\
                    memaccess_inbounds e2
                     [inp,len; c,192; out,64;
                      word(pc + sha3_keccak_f1600_alt2_rotations),384;
                      word_sub stackpointer (word 256),264]
                     [out,64; word_sub stackpointer (word 256),256]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(out,64);
               memory :> bytes(word_sub stackpointer (word 256),256)])`,
  ASSUME_CALLEE_TAILED_TAC MLKEM_HASH_G_WORDS_FULL "H_W" THEN
  ASSUME_CALLEE_TAILED_TAC MLKEM_HASH_G_BYTES_FULL "H_B" THEN
  ASSUME_CALLEE_TAILED_TAC MLKEM_HASH_G_PAD_FULL "H_P" THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `out:int64`; `inp:int64`; `m:byte list`;
    `len:num`; `c:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 256 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `len < 2 EXP 64` ASSUME_TAC THENL
   [UNDISCH_TAC `len < 72` THEN ARITH_TAC; ALL_TAC] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORDLIST_FROM_MEMORY_ROUND_CONSTANTS]) THEN
  X86_STEPS_TAC MLKEM_HASH_G_EXEC (1--18) THEN
  SUBGOAL_THEN
   `read (memory :> wbytes (word_add stackpointer (word 8))) s18 =
    (word 0:1600 word)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC READ_MEMORY_WBYTES_ZERO THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[WORD_ADD_0];
    ALL_TAC] THEN
  HG_LEMMA_CALL_TAC "H_W"
   [`m:byte list`; `inp:int64`; `c:int64`; `pc:num`;
    `word_add stackpointer (word 8):int64`; `0`; `len:num`;
    `word 0:1600 word`] 19 THEN
  HG_LEMMA_CALL_TAC "H_B"
   [`m:byte list`; `inp:int64`; `c:int64`; `pc:num`;
    `word_add stackpointer (word 8):int64`; `0`; `len:num`;
    `word 0:1600 word`] 20 THEN
  HG_LEMMA_CALL_TAC "H_P"
   [`inp:int64`; `len:num`; `c:int64`; `pc:num`;
    `word_add stackpointer (word 8):int64`; `len:num`;
    `word_xor (word 0) (word(num_of_bytelist(m:byte list))):1600 word`;
    `num_of_bytelist(m:byte list)`] 21 THEN
  SUBGOAL_THEN `LENGTH(m:byte list) DIV 72 = 0 /\ len DIV 72 = 0 /\
                LENGTH(m:byte list) MOD 72 = len /\ len MOD 72 = len`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC DIV_LT) THEN TRY(MATCH_MP_TAC MOD_LT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `keccak_f1600
     (word_xor
       (keccak_absorb 72 (keccak_padded 72 6 m) (LENGTH(m:byte list) DIV 72))
       (word((keccak_padded 72 6 m DIV
              2 EXP (8 * 72 * LENGTH m DIV 72)) MOD 2 EXP (8 * 72)))) =
    keccak_f1600(((word 0 ^^ word(num_of_bytelist m)) ^^
                  word(2 EXP (8 * len) * 6)) ^^ word(2 EXP (8 * 71) * 128))`
  ASSUME_TAC THENL
   [AP_TERM_TAC THEN
    SIMP_TAC[KECCAK_LAST_BLOCK_XOR; ARITH_RULE `0 < 72 /\ 6 < 128`] THEN
    ASM_REWRITE_TAC[CONJUNCT1 keccak_absorb; MULT_CLAUSES; EXP; DIV_1;
                    ARITH_RULE `72 - 1 = 71`; WORD_XOR_ASSOC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) &&
       can (term_match [] `keccak_f1600 x = keccak_f1600 y`) (concl th)
    then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) else NO_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (can (term_match []
    `read (memory :> wbytes a) s21 = keccak_f1600 x`) o concl)) THEN
  ABBREV_TAC
   `S = keccak_f1600
         (word_xor
           (keccak_absorb 72 (keccak_padded 72 6 m) (LENGTH m DIV 72))
           (word((keccak_padded 72 6 m DIV
                  2 EXP (8 * 72 * LENGTH m DIV 72)) MOD 2 EXP (8 * 72))))`
  THEN
  REWRITE_TAC[READ_MEMORY_WBYTES_1600] THEN DISCH_TAC THEN
  MAP_EVERY (fun k ->
    MP_TAC(SPECL [`word_add stackpointer (word 8):int64`; `200`;
                  `val(S:1600 word)`; k; `s21:x86state`]
      READ_MEMORY_BYTES256_OF_NUM))
   [`0`; `32`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  REWRITE_TAC[WORD_ADD_0; DIV_1] THEN REPEAT DISCH_TAC THEN
  X86_STEPS_TAC MLKEM_HASH_G_EXEC (22--40) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`out:int64`; `2`; `val(S:1600 word)`; `s40:x86state`]
      READ_MEMORY_BYTES_OF_BYTES256) THEN
    CONV_TAC(LAND_CONV(LAND_CONV EXPAND_CASES_CONV)) THEN
    CONV_TAC(LAND_CONV(LAND_CONV NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[ARITH_RULE `32 * 2 = 64 /\ 256 * 2 = 512`] THEN
    ASM_REWRITE_TAC[WORD_ADD_0; DIV_1] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[sha3_512] THEN
    MP_TAC(SPECL [`1024`; `6`; `m:byte list`; `72`; `keccak_padded 72 6 m`;
                  `64`] KECCAK_SPONGE_BYTES) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[keccak_padded] THEN CONV_TAC NUM_REDUCE_CONV;
      DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[ARITH_RULE `8 * 64 = 512`];
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The calls of the functions of the image by their safety theorems: the     *)
(* arguments from the registers, the image addresses and alignments first,   *)
(* the stack pointer after the return simplified.                            *)
(* ------------------------------------------------------------------------- *)

(*** The goal of the events before a call (e_tail), with that of the
 *** stack argument (at the stack pointer of the callee + 8) when it has
 *** one, as word_add (word_sub fb (word 8)) (word 8)
 ***)

let API_SAFE_E2_TAC vs =
  let side =
    REWRITE_TAC[API_WORD_SUB_ADD] THEN ASM_REWRITE_TAC[] THEN NO_TAC in
  (CONJ_TAC THEN FIRST [side; EXISTS_E2_TAC (ref vs)]) ORELSE
  EXISTS_E2_TAC (ref vs);;

let API_SAFE_THM_TAC exec vars label (offset,submc) f ilist k gl =
  let vs = vars @ fev_vars gl in
  REMOVE_THEN label (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
     (mlkem_native2_image_mc,exec,offset,submc,FRESH_TAIL_RULE(f th))
     ilist (k+1)
    THENL [API_SAFE_E2_TAC vs; LABEL_TAC label th]) gl;;

let API_SAFE_SIM_TAC exec vars label args k =
  API_SAFE_THM_TAC exec vars label (0,mlkem_native2_image_mc)
   (fun th -> CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
               (REWRITE_RULE[LENGTH_MLKEM_G; LENGTH_MLKEM_SLICE]
                 (SPECL (`e:(uarch_event)list` :: args) th)))
   [] k;;

let API_PKE_SAFE_CALL_TAC exec vars label regs kk gl =
  let r c = find_read_fact c kk gl in
  (API_SAFE_PRE_TAC kk THEN
   API_SAFE_SIM_TAC exec vars label
    (map r regs @ [`pc:num`; r `RSP`; api_ret kk gl]) kk THEN
   API_RSP_TAC) gl;;

let API_HASH_G_SAFE_CALL_TAC exec vars label kk gl =
  let r c = find_read_fact c kk gl in
  let len = mk_small_numeral(dest_small_numeral(rand(r `RDX`))) in
  (API_SAFE_PRE_TAC kk THEN
   API_SAFE_SIM_TAC exec vars label
    [r `RDI`; r `RSI`; len; r `RCX`; `pc:num`; r `RSP`; api_ret kk gl] kk THEN
   API_RSP_TAC) gl;;

let API_GETNOISE_SAFE_CALL_TAC exec vars kk gl =
  let r c = find_read_fact c kk gl in
  let v reg = mk_small_numeral(dest_small_numeral(rand(r reg))) in
  let vs = vars @ fev_vars gl in
  (API_SAFE_PRE_TAC kk THEN
   API_CONSTS_TAC kk THEN
   REMOVE_THEN "H_GETNOISE" (fun th ->
     let th1 = SPECL [`e:(uarch_event)list`; r `RDI`; r `RSI`; v `RDX`;
                      v `RCX`; v `R8`; v `R9`; r `R15`; `pc:num`; r `RSP`;
                      api_ret kk gl] th in
     let th2 = CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
                (REWRITE_RULE[ARITH_EQ] th1) in
     X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native2_image_mc,exec,0,mlkem_native2_image_mc,
       FRESH_TAIL_RULE th2) [] (kk+1)
     THENL [API_SAFE_E2_TAC vs; LABEL_TAC "H_GETNOISE" th]) THEN
   API_RSP_TAC) gl;;

(*** Abbreviations: the assumptions t = v with v a variable named in names
 *** used to rewrite the others, so that the events are functions of v
 ***)

let ABBREVS_TAC names (asl,w as gl) =
  let abs = filter (fun (_,th) ->
    let c = concl th in
    is_eq c && is_var(rand c) && mem (name_of(rand c)) names &&
    not(is_var(lhand c))) asl in
  let ths = map snd abs in
  RULE_ASSUM_TAC(fun th -> if mem (concl th) (map concl ths) then th
                           else REWRITE_RULE ths th) gl;;

(* ------------------------------------------------------------------------- *)
(* dec: K-PKE.Decrypt, G, the matrix with H(ek) as a result, ek and h as     *)
(* variables for the events, the hash check and the case split on it; then   *)
(* K-PKE.Encrypt, the comparison and the selection.                          *)
(* ------------------------------------------------------------------------- *)

let de_ek k = parse_term("mlkem_slice "^string_of_int(384 * k)^" "^
                         string_of_int(384 * k + 32)^" dk");;
let de_h k = parse_term("mlkem_slice "^string_of_int(768 * k + 32)^" 32 dk");;
let de_rho_ek k =
  parse_term("mlkem_slice "^string_of_int(384 * k)^" 32 ek");;

let de_rho_eq k =
  let tm = parse_term("mlkem_slice "^string_of_int(384 * k)^
    " 32 (mlkem_slice "^
    string_of_int(384 * k)^" "^string_of_int(384 * k + 32)^" dk) = "^
    "mlkem_slice "^string_of_int(768 * k)^" 32 dk") in
  prove(tm,
    SIMP_TAC[MLKEM_SLICE_SLICE; ARITH] THEN CONV_TAC NUM_REDUCE_CONV);;

let api_wadd a n = mk_comb(mk_comb(`word_add:int64->int64->int64`,a),
                           mk_comb(`word:num->int64`,mk_small_numeral n));;

(*** gen_matrix by its theorem with H(ek) as a result: rho, ek at
 *** sk + 384 * k as variables
 ***)

let DE_GM_SAFE_CALL_TAC exec vars k kk gl =
  let r c = find_read_fact c kk gl in
  let fb = `fb:int64` in
  let args =
    [r `RDI`; r `RSI`; de_rho_ek k; r `R8`;
     api_wadd `sk:int64` (384 * k); `ek:byte list`;
     api_wadd fb de_hek; api_wadd fb de_zc; api_wadd fb de_j; r `R9`] @
    (if k = 2 then []
     else [api_wadd fb (de_kr + 32); api_wadd fb (de_noise k)]) @
    [api_c_tm; `pc:num`; r `RSP`; api_ret kk gl] in
  (API_SLICE_AT_TAC `sk:int64` `dk:byte list` (768 * k) 32 kk THEN
   API_SLICE_AT_TAC `sk:int64` `dk:byte list` (384 * k) (384 * k + 32) kk THEN
   RULE_ASSUM_TAC(REWRITE_RULE[GSYM(de_rho_eq k)]) THEN
   ABBREVS_TAC ["ek"; "h"] THEN
   API_CONSTS_TAC kk THEN API_SAFE_PRE_TAC kk THEN
   API_SAFE_SIM_TAC exec vars "H_GM" args kk THEN API_RSP_TAC) gl;;

(*** The digest and h as 64-bit words at state kk, for the hash check ***)

let DE_DIGITS_TAC k kk =
  BIGDIGITS_32_TAC (api_wadd `fb:int64` de_hek)
   `num_of_bytelist(sha3_256 ek)` (state_of kk) THEN
  API_SLICE_AT_TAC `sk:int64` `dk:byte list` (768 * k + 32) 32 kk THEN
  ABBREVS_TAC ["ek"; "h"] THEN
  BIGDIGITS_32_TAC (api_wadd `sk:int64` (768 * k + 32))
   `num_of_bytelist(h:byte list)` (state_of kk);;

(*** The branch of the hash check at state kk as sha3_256 ek = h ***)

let DE_HASH_SAFE_BRANCH_TAC kk =
  let sv = state_of kk in
  let bnd l =
    let th = ISPEC l NUM_OF_BYTELIST_BOUND in
    CONV_RULE NUM_REDUCE_CONV
     (REWRITE_RULE[LENGTH_SHA3_256; ASSUME `LENGTH(h:byte list) = 32`] th) in
  let hek = `sha3_256 ek` and h = `h:byte list` in
  let lenth = TRANS (ISPEC `ek:byte list` LENGTH_SHA3_256)
                    (SYM(ASSUME `LENGTH(h:byte list) = 32`)) in
  let inj = MP (ISPECL [hek; h] NUM_OF_BYTELIST_INJ) lenth in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && lhand c = mk_comb(`read RIP`,sv) then
      let vt = find_term (can (term_match [] `val(x:int64) = 0`)) c in
      let eth = PART_MATCH (lhand o rand) WORD_OR_XOR_DIGITS_EQ_0 vt in
      let eth' = MP (CONV_RULE(RATOR_CONV(RAND_CONV NUM_REDUCE_CONV)) eth)
                    (CONJ (bnd hek) (bnd h)) in
      ASSUME_TAC(REWRITE_RULE[eth'; inj] th)
    else NO_TAC);;

let de_safe_parts k ex gmth (pdth,peth) =
  let nm = api_param k in
  let zs = api_zero_loops (nm ^ "_dec") in
  let zths = map (API_ZERO_SAFE_LOOP ex) zs in
  let zlabels = ["H_ZV"; "H_ZI"] in
  let vars = [`ss:int64`; `ct:int64`; `sk:int64`; `pc:num`;
              `stackpointer:int64`; `returnaddress:int64`;
              `ek:byte list`; `h:byte list`; `fb:int64`; `delta:num`] in
  let zil = [`e:(uarch_event)list`; `read RDI s`; `pc:num`] in
  let calls =
    api_safe_calls ex vars [] (map2 (fun (lo,_) l -> lo - 5,l,zil) zs zlabels)
    @ [layout (nm ^ "_pke_decrypt"),
         API_PKE_SAFE_CALL_TAC ex vars "H_PD" [`RDI`; `RSI`; `RDX`];
       layout "mlkem_hash_g", API_HASH_G_SAFE_CALL_TAC ex vars "H_HGS";
       layout "mlkem_gen_matrix",
         (fun kk -> DE_GM_SAFE_CALL_TAC ex vars k kk THEN
                    (if k = 2 then ALL_TAC else DE_DIGITS_TAC k (kk+1)));
       layout "mlkem_getnoise",
         (fun kk -> API_GETNOISE_SAFE_CALL_TAC ex vars kk THEN
                    DE_DIGITS_TAC k (kk+1));
       layout (nm ^ "_pke_encrypt"),
         API_PKE_SAFE_CALL_TAC ex vars "H_PE"
          [`RDI`; `RSI`; `RDX`; `RCX`; `R8`]] in
  let setup =
    API_SAFE_ASSUME_TAC [] (zip zlabels zths) THEN
    ASSUME_CALLEE_TAILED_TAC pdth "H_PD" THEN
    ASSUME_CALLEE_TAILED_TAC MLKEM_HASH_G_SUBROUTINE_SAFE "H_HGS" THEN
    ASSUME_CALLEE_TAILED_TAC gmth "H_GM" THEN
    ASSUME_CALLEE_TAILED_TAC MLKEM_GETNOISE_SUBROUTINE_SAFE "H_GETNOISE" THEN
    ASSUME_CALLEE_TAILED_TAC peth "H_PE" THEN
    CONCRETIZE_F_EVENTS_TAC
     `\(ss:int64) (ct:int64) (sk:int64) (pc:num) (stackpointer:int64)
       (returnaddress:int64) (ek:byte list) (h:byte list).
        if sha3_256 ek = h
        then f_ev_ok ss ct sk pc stackpointer returnaddress ek h
        else f_ev_bad ss ct sk pc stackpointer returnaddress ek h
        :(uarch_event)list` THEN
    REPEAT META_EXISTS_TAC THEN
    API_SAFE_ENTRY_TAC ex
     [`e:(uarch_event)list`; `ss:int64`; `ct:int64`; `sk:int64`;
      `dk:byte list`; `pc:num`] (de_stack k) (de_frame k) THEN
    ASSUME_TAC(ISPECL [mk_small_numeral(384 * k);
                       mk_small_numeral(384 * k + 32); `dk:byte list`]
                      LENGTH_MLKEM_SLICE) THEN
    ASSUME_TAC(ISPECL [mk_small_numeral(768 * k + 32); `32`; `dk:byte list`]
                      LENGTH_MLKEM_SLICE) THEN
    ABBREV_TAC(mk_eq(`ek:byte list`,de_ek k)) THEN
    ABBREV_TAC(mk_eq(`h:byte list`,de_h k)) THEN
    ABBREVS_TAC ["ek"; "h"] in
  setup,calls;;

let MLKEM_NATIVE2_DEC_SAFE_TAC k ex gmth (pdth,peth) =
  let setup,calls = de_safe_parts k ex gmth (pdth,peth) in
  setup THEN NATIVE2_SAFE_RUN_TAC ex [] calls 11 THEN
  ON_STATE DE_HASH_SAFE_BRANCH_TAC THEN
  API_BOOL_CASE_TAC `sha3_256 ek = h` THEN
  ON_STATE(NATIVE2_SAFE_RUN_TAC ex [] calls) THEN API_SAFE_FINAL_TAC;;

(* ------------------------------------------------------------------------- *)
(* enc_derand: the modulus check by its FULL theorem and the case split on   *)
(* it; then the matrix with H(ek), G, the noise and K-PKE.Encrypt.           *)
(* ------------------------------------------------------------------------- *)

(*** The modulus check of ek at RDI by the FULL theorem, the result as
 *** mlkem_ek_check
 ***)

let API_CHECK_ENCODING_FULL_CALL_TAC exec vars k ek kk gl =
  let a = find_read_fact `RDI` kk gl in
  let n = mk_comb(`num_of_bytelist`,
            list_mk_icomb "mlkem_slice"
             [`0`; mk_small_numeral(384 * k); ek]) in
  let vs = vars @ fev_vars gl in
  let eks = ek_check_slice k in
  let lenth = find_asm (fun c ->
    c = mk_eq(mk_comb(`LENGTH:byte list->num`,ek),
              mk_small_numeral(kp_pkb k))) gl in
  (API_SLICE_AT_TAC a ek 0 (384 * k) kk THEN
   REMOVE_THEN "H_CE" (fun th ->
     let th1 = SPECL [`e:(uarch_event)list`; a;
                      mk_comb(`word:num->int64`,mk_small_numeral k); n;
                      `pc + mlkem_check_encoding`;
                      find_read_fact `RSP` kk gl; api_ret kk gl] th in
     let th2 = REWRITE_RULE[ARITH_RULE `4096 = 2 EXP 12`]
                (CONV_RULE(ONCE_DEPTH_CONV WORD_NUM_RED_CONV THENC
                           ONCE_DEPTH_CONV NUM_MULT_CONV) th1) in
     X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native2_image_mc,exec,layout "mlkem_check_encoding",
       mlkem_check_encoding_mc,FRESH_TAIL_RULE th2) [] (kk+1)
     THENL [EXISTS_E2_TAC (ref vs); LABEL_TAC "H_CE" th]) THEN
   API_RSP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP eks lenth])) gl;;

(*** gen_matrix by its safety theorem, with rho from ek and H(ek) as job 1 ***)

let EN_GM_SAFE_CALL_TAC exec vars k kk gl =
  let r c = find_read_fact c kk gl in
  let rho = parse_term("mlkem_slice "^string_of_int(384 * k)^" 32 ek") in
  let args =
    [r `RDI`; r `RSI`; rho; r `R8`; `word 0:int64`; `word 0:int64`;
     `word 0:int64`; `pk:int64`; api_wadd `fb:int64` (en_gin + 32); r `R9`;
     api_c_tm; `pc:num`; r `RSP`; api_ret kk gl] in
  (API_SLICE_AT_TAC `pk:int64` `ek:byte list` (384 * k) 32 kk THEN
   API_CONSTS_TAC kk THEN API_SAFE_PRE_TAC kk THEN
   API_SAFE_SIM_TAC exec vars "H_GM" args kk THEN API_RSP_TAC) gl;;

let en_safe_parts k ex gmth peth =
  let nm = api_param k in
  let zs = api_zero_loops (nm ^ "_enc_derand") in
  let zths = map (API_ZERO_SAFE_LOOP ex) zs in
  let zlabels = map (fun i -> "H_Z"^string_of_int i) (0--(length zs - 1)) in
  let vars = [`ct:int64`; `ss:int64`; `pk:int64`; `coins:int64`; `pc:num`;
              `stackpointer:int64`; `returnaddress:int64`; `ek:byte list`;
              `fb:int64`; `delta:num`] in
  let zil = [`e:(uarch_event)list`; `read RDI s`; `pc:num`] in
  let calls =
    api_safe_calls ex vars [] (map2 (fun (lo,_) l -> lo - 5,l,zil) zs zlabels)
    @ [layout "mlkem_check_encoding",
         API_CHECK_ENCODING_FULL_CALL_TAC ex vars k `ek:byte list`;
       layout "mlkem_gen_matrix", EN_GM_SAFE_CALL_TAC ex vars k;
       layout "mlkem_hash_g", API_HASH_G_SAFE_CALL_TAC ex vars "H_HGS";
       layout "mlkem_getnoise", API_GETNOISE_SAFE_CALL_TAC ex vars;
       layout (nm ^ "_pke_encrypt"),
         API_PKE_SAFE_CALL_TAC ex vars "H_PE"
          [`RDI`; `RSI`; `RDX`; `RCX`; `R8`]] in
  let setup =
    API_SAFE_ASSUME_TAC [] (zip zlabels zths) THEN
    ASSUME_CALLEE_TAILED_TAC MLKEM_CHECK_ENCODING_SUBROUTINE_FULL "H_CE" THEN
    ASSUME_CALLEE_TAILED_TAC gmth "H_GM" THEN
    ASSUME_CALLEE_TAILED_TAC MLKEM_HASH_G_SUBROUTINE_SAFE "H_HGS" THEN
    ASSUME_CALLEE_TAILED_TAC MLKEM_GETNOISE_SUBROUTINE_SAFE "H_GETNOISE" THEN
    ASSUME_CALLEE_TAILED_TAC peth "H_PE" THEN
    CONCRETIZE_F_EVENTS_TAC (parse_term(
     "\\(ct:int64) (ss:int64) (pk:int64) (coins:int64) (pc:num) "^
     "  (stackpointer:int64) (returnaddress:int64) (ek:byte list). "^
     "  if mlkem_ek_check "^nm^" ek "^
     "  then f_ev_ok ct ss pk coins pc stackpointer returnaddress ek "^
     "  else f_ev_bad ct ss pk coins pc stackpointer returnaddress ek "^
     "  :(uarch_event)list")) THEN
    REPEAT META_EXISTS_TAC THEN
    API_SAFE_ENTRY_TAC ex
     [`e:(uarch_event)list`; `ct:int64`; `ss:int64`; `pk:int64`;
      `coins:int64`; `ek:byte list`; `pc:num`] (en_stack k) (en_frame k) in
  setup,calls;;

(*** The branch on the result of the check, before the case split ***)

let EN_CHECK_BRANCH = prove
 (`!b. val(if b then word 1 else word 0:int64) = 0 <=> ~b`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV));;

let MLKEM_NATIVE2_ENC_DERAND_SAFE_TAC k ex gmth peth =
  let setup,calls = en_safe_parts k ex gmth peth in
  setup THEN NATIVE2_SAFE_RUN_TAC ex [] calls 11 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EN_CHECK_BRANCH]) THEN
  API_BOOL_CASE_TAC (parse_term("mlkem_ek_check "^api_param k^" ek")) THEN
  ON_STATE(NATIVE2_SAFE_RUN_TAC ex [] calls) THEN API_SAFE_FINAL_TAC;;

(* ------------------------------------------------------------------------- *)
(* keypair_derand: G(d || k) by its FULL theorem, rho as a variable for the  *)
(* events, the matrix and the noise, the NTT domain and the encodings, the   *)
(* copy into sk with H(pk) and z, and rho in pk.                             *)
(* ------------------------------------------------------------------------- *)

(*** rho = FST(mlkem_g(d || k)) as a variable (an abbreviation), so that
 *** the events are a function of it: the assumptions rewritten with it
 ***)

let KP_RHO_ABBREV_TAC (asl,w as gl) =
  let ab = find_asm (fun c ->
    is_eq c && is_var(rand c) && name_of(rand c) = "rho" &&
    can (find_term (fun t -> try fst(dest_const t) = "mlkem_g"
                             with Failure _ -> false)) (lhand c)) gl in
  RULE_ASSUM_TAC(fun th -> if concl th = concl ab then th
                           else REWRITE_RULE[ab] th) gl;;

(*** G = SHA3-512 on d || k by the FULL theorem, then rho and sigma, rho as
 *** a 256-bit word for its copy into pk
 ***)

let KP_HG_SAFE_CALL_TAC exec vars k kk gl =
  let d = `d:byte list` in
  let r c = find_read_fact c kk gl in
  let a = r `RSI` and sv = state_of kk in
  let kb = mk_comb(`word:num->byte`,mk_small_numeral k) in
  let m = mk_comb(mk_comb(`APPEND:byte list->byte list->byte list`,d),
                  mk_list([kb],`:byte`)) in
  let ldth = find_asm (fun c -> c = `LENGTH(d:byte list) = 32`) gl in
  let lenth = (REWRITE_CONV[LENGTH_APPEND; LENGTH; ldth] THENC
               NUM_REDUCE_CONV) (mk_comb(`LENGTH:byte list->num`,m)) in
  (MP_TAC(SPECL [a; d; kb; sv] READ_MEMORY_BYTES_33_OF_256) THEN
   ANTS_TAC THENL
    [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
     CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN ASM_REWRITE_TAC[] THEN NO_TAC;
     DISCH_TAC] THEN
   ASSUME_TAC lenth THEN
   ASSUME_TAC(CONJUNCT1(ISPEC m LENGTH_MLKEM_G)) THEN
   API_CONSTS_TAC kk THEN API_SAFE_PRE_TAC kk THEN
   API_SAFE_SIM_TAC exec vars "H_HG"
    [r `RDI`; a; m; `33`; r `RCX`; `pc:num`; r `RSP`; api_ret kk gl] kk THEN
   API_RSP_TAC THEN
   API_G_SPLIT_TAC (kk+1) THEN
   KP_RHO_ABBREV_TAC THEN
   API_BYTES256_OF_TAC (api_wadd `fb:int64` kp_g)
    `num_of_bytelist(rho:byte list)` 32 0 (kk+1)) gl;;

(*** gen_matrix by its safety theorem: k = 2 without noise, else with the
 *** noise of s and e
 ***)

let KP_GM_SAFE_CALL_TAC exec vars k kk gl =
  let r c = find_read_fact c kk gl in
  let fb = `fb:int64` in
  let args =
    if k = 2 then
      [r `RDI`; r `RSI`; `rho:byte list`; r `R8`; r `R9`;
       api_c_tm; `pc:num`; r `RSP`; api_ret kk gl]
    else
      [r `RDI`; r `RSI`; `rho:byte list`; r `R9`;
       api_wadd fb (kp_g + 32); api_wadd fb (kp_s k); r `R8`;
       api_c_tm; `pc:num`; r `RSP`; api_ret kk gl] in
  (API_CONSTS_TAC kk THEN API_SAFE_PRE_TAC kk THEN
   API_SAFE_SIM_TAC exec vars "H_GM" args kk THEN API_RSP_TAC) gl;;

let kp_safe_parts k ex gmth =
  let nm = api_param k in
  let names = ["mlkem_ntt_x86"; "mlkem_mulcache_compute_x86";
               "mlkem_basemul_k"^string_of_int k; "mlkem_tomont";
               "mlkem_add_reduce"; "mlkem_reduce"; "mlkem_tobytes"] in
  let zs = api_zero_loops (nm ^ "_keypair_derand") in
  let zths = map (API_ZERO_SAFE_LOOP ex) zs in
  let zlabels = map (fun i -> "H_Z"^string_of_int i) (0--(length zs - 1)) in
  let vars = [`pk:int64`; `sk:int64`; `coins:int64`; `pc:num`;
              `stackpointer:int64`; `returnaddress:int64`; `rho:byte list`;
              `fb:int64`; `delta:num`] in
  let zil = [`e:(uarch_event)list`; `read RDI s`; `pc:num`] in
  let calls =
    api_safe_calls ex vars names
      (map2 (fun (lo,_) l -> lo - 5,l,zil) zs zlabels) @
    [layout "mlkem_hash_g", KP_HG_SAFE_CALL_TAC ex vars k;
     layout "mlkem_gen_matrix", KP_GM_SAFE_CALL_TAC ex vars k;
     layout "mlkem_getnoise", API_GETNOISE_SAFE_CALL_TAC ex vars;
     layout "mlkem_hash_h", API_HASH_G_SAFE_CALL_TAC ex vars "H_HH"] in
  let setup =
    API_SAFE_ASSUME_TAC names (zip zlabels zths) THEN
    ASSUME_CALLEE_TAILED_TAC MLKEM_HASH_G_SHORT_SUBROUTINE_FULL "H_HG" THEN
    ASSUME_CALLEE_TAILED_TAC gmth "H_GM" THEN
    ASSUME_CALLEE_TAILED_TAC MLKEM_GETNOISE_SUBROUTINE_SAFE "H_GETNOISE" THEN
    ASSUME_CALLEE_TAILED_TAC MLKEM_HASH_H_SUBROUTINE_SAFE "H_HH" THEN
    META_EXISTS_TAC THEN
    API_SAFE_ENTRY_TAC ex
     [`e:(uarch_event)list`; `pk:int64`; `sk:int64`; `coins:int64`;
      `d:byte list`; `pc:num`] (kp_stack k) (kp_frame k) THEN
    ABBREV_TAC(mk_eq(`rho:byte list`,kp_rho k)) THEN
    ON_STATE(API_BYTES256_OF_TAC `coins:int64`
              `num_of_bytelist(d:byte list)` 32 0)
  and finish =
    ON_STATE(API_JOIN256_TAC (api_wadd `pk:int64` (384 * k))
              `rho:byte list` 1) THEN
    API_SAFE_FINAL_TAC in
  setup,calls,finish;;

let MLKEM_NATIVE2_KEYPAIR_DERAND_SAFE_TAC k ex gmth =
  let setup,calls,finish = kp_safe_parts k ex gmth in
  setup THEN NATIVE2_SAFE_RUN_TAC ex [] calls 11 THEN finish;;
