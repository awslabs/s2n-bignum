(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The main lemma and the top level of mldsa{44,65,87}_poly_uniform_eta_4x  *)
(* of the clang 23 -O3 build (44 and 87 have the same code with eta = 2; 65  *)
(* has eta = 4 and squeezes two blocks in the first pass), from the region   *)
(* lemmas of inline_eta4x.ml. The structure is that of the   *)
(* gcc proof gcc12_O2_reduced_ram/poly_uniform_eta_4x_44_proof.ml: the       *)
(* number k0 of extra blocks is the least n after which all four            *)
(* polynomials have 256 coefficients, and the loop over the blocks runs k0  *)
(* times.                                                                    *)
(*                                                                           *)
(* This file is loaded with loadt, not needs, after binding                 *)
(*   EM_EXEC: the EXEC theorem of the function,                             *)
(*   EM_B:    the offset of the function in the image,                      *)
(*   EM_L:    its region lemmas (ETA2_PROVE_ALL EM_EXEC EM_B),              *)
(*   EM_P:    the parameters of the code (ETA2_MAIN_PAR of inline_eta4x.ml), *)
(* as the tactics are specialized to them when they are defined.            *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* MAIN: from the stack probe at +0x24 to the stack check (+0xa1c in 44),   *)
(* the frame fr = sp - 240 of the aligned stack pointer sp (the callee        *)
(* permute uses the 240 bytes below sp) and fp = X29 (the fourth nonce is at  *)
(* fp + 96).                                                                  *)
(* ------------------------------------------------------------------------- *)

(* placeholders for the parameters in the terms below: FIRST (the bytes of
   the first pass), NB (its blocks) and ETA *)
let EM_INST tm =
  vsubst [mk_small_numeral EM_P.m_first,`FIRST:num`;
          mk_small_numeral (EM_P.m_first / 136),`NB:num`;
          mk_small_numeral EM_P.m_eta,`ETA:num`] tm;;

let EM_ETA = mk_small_numeral EM_P.m_eta;;

let ETA_MAIN_TM b eta =
  let nonce k = if k = 3 then "n3:byte" else Printf.sprintf "word_zx(n%d:int64):byte" k in
  let str k = Printf.sprintf "mld_shake256_stream 66 (sd + 2 EXP 512 * val(%s))" (nonce k) in
  let term k = Printf.sprintf "mld_rej_eta_terminates %d (%s)" eta (str k) in
  let poly k = Printf.sprintf
    "(!i. i < 256 ==> read(memory :> bytes32(word_add r%d (word(4 * i)))) s = mld_poly_uniform_eta %d sd (%s) i)"
    k eta (if k = 3 then "n3" else Printf.sprintf "word_zx n%d" k) in
  let dcl k = Printf.sprintf "(mld_poly_uniform_eta_declass %d (%s))" eta (str k) in
  parse_term(Printf.sprintf
  "!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e r0 r1 r2 r3 seed sd n0 n1 n2 n3 guard canary fp fr pc.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          aligned 16 (word_add fr (word 240):int64) /\\ aligned 32 (word_add fr (word 240):int64) /\\
          %s /\\ %s /\\ %s /\\ %s /\\
          PAIRWISE nonoverlapping
           [(r0,1024); (r1,1024); (r2,1024); (r3,1024); (fr,%d)] /\\
          ALLPAIRS nonoverlapping
           [(r0,1024); (r1,1024); (r2,1024); (r3,1024); (fr,%d)]
           [(seed,64); (word_add fp (word 96),1);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\\s. aligned_bytes_loaded s (word pc) %s /\\
                    read PC s = word (pc + %d) /\\
                    read SP s = word_add fr (word 240) /\\ read X29 s = fp /\\
                    C_ARGUMENTS [r0; r1; r2; r3; seed; n0; n1; n2] s /\\
                    read (memory :> bytes8 (word_add fp (word 96))) s = n3 /\\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s = guard /\\
                    read (memory :> bytes64 guard) s = canary /\\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                    read (memory :> bytes(ea,el)) s = ev /\\
                    read (memory :> bytes(seed,64)) s = sd /\\
                    read events s = e)
               (\\s. read PC s = word (pc + %d) /\\
                    read SP s = word_add fr (word 240) /\\ read X29 s = fp /\\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s = guard /\\
                    read (memory :> bytes64 guard) s = canary /\\
                    read (memory :> bytes64 (word_add fr (word %d))) s = canary /\\
                    %s /\\ %s /\\ %s /\\ %s /\\
                    (exists e2.
                       read events s = APPEND e2 e /\\
                       e2 = f_events r0 r1 r2 r3 seed %s %s %s %s guard mf pc fp fr /\\
                       memaccess_inbounds e2
                        [seed,64; word_add fp (word 96),1;
                         r0,1024; r1,1024; r2,1024; r3,1024; fr,%d;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [r0,1024; r1,1024; r2,1024; r3,1024; fr,%d]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
                MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28] ,,
                MAYCHANGE
                 [memory :> bytes(r0,1024); memory :> bytes(r1,1024);
                  memory :> bytes(r2,1024); memory :> bytes(r3,1024);
                  memory :> bytes(fr,%d)])"
   (term 0) (term 1) (term 2) (term 3) EM_P.m_frlen EM_P.m_frlen ETA_MC (b + 0x24)
   (b + EM_P.m_pend) EM_P.m_canary (poly 0) (poly 1) (poly 2) (poly 3)
   (dcl 0) (dcl 1) (dcl 2) (dcl 3) EM_P.m_frlen EM_P.m_frlen EM_P.m_frlen);;

(* ------------------------------------------------------------------------- *)
(* The events template: P1 (up to the first test), the loop over k0 extra     *)
(* blocks (k0 = 0 skips it), P3 (the zeroing). The setup: the declassified   *)
(* lists dc0..dc3, the absorbed states S0..S3, k0 as the least number of      *)
(* extra blocks after which every polynomial has 256 coefficients.            *)
(* ------------------------------------------------------------------------- *)

let EM_NONCES = [`word_zx(n0:int64):byte`; `word_zx(n1:int64):byte`; `word_zx(n2:int64):byte`; `n3:byte`]
and EM_DS = [`dc0:bool list`; `dc1:bool list`; `dc2:bool list`; `dc3:bool list`]
and EM_VECS = [`r0:int64`; `r1:int64`; `r2:int64`; `r3:int64`]
and EM_SVS = [`S0:1600 word`; `S1:1600 word`; `S2:1600 word`; `S3:1600 word`];;

let em_input h = vsubst [h,`h:byte`] `sd + 2 EXP 512 * val(h:byte)`;;

let em_stream h = mk_comb(`mld_shake256_stream 66`,em_input h);;

let em_declass h = mk_comb(mk_comb(`mld_poly_uniform_eta_declass`,EM_ETA),em_stream h);;

let EM_DONE n =
  list_mk_conj
   (map (fun d -> vsubst [d,`D:bool list`; n,`n:num`]
          (EM_INST `256 <= LENGTH(FILTER (\x:bool. x) (SUB_LIST(0,2 * (FIRST + 136 * n)) D))`))
        EM_DS);;

let EM_ARGS = [`r0:int64`; `r1:int64`; `r2:int64`; `r3:int64`; `seed:int64`;
  `dc0:bool list`; `dc1:bool list`; `dc2:bool list`; `dc3:bool list`;
  `guard:int64`; `mf:int64`; `pc:num`; `fp:int64`; `fr:int64`];;

let EM_TEMPLATE =
  let args = EM_ARGS in
  let fty = itlist (fun a t -> mk_fun_ty (type_of a) t) args `:(uarch_event)list` in
  let fv n = mk_var(n,fty) in
  let app n = list_mk_comb(fv n,args) in
  let k0 = mk_comb(`(minimal):(num->bool)->num`, mk_abs(`n:num`,EM_DONE `n:num`)) in
  let fl = list_mk_comb(mk_var("f_ev_loop",
             itlist (fun a t -> mk_fun_ty (type_of a) t) args
                    (mk_fun_ty `:num` `:(uarch_event)list`)),args) in
  let loop = mk_abs(`i:num`,mk_comb(fl,`i:num`)) in
  let ap = `APPEND:(uarch_event)list->(uarch_event)list->(uarch_event)list` in
  let enum = list_mk_comb(`ENUMERATEL:num->(num->(uarch_event)list)->(uarch_event)list`,[k0;loop]) in
  let mid = mk_cond(mk_eq(k0,`0`),app "f_ev_skip",
              list_mk_comb(ap,[app "f_ev_exit"; list_mk_comb(ap,[enum; app "f_ev_enter"])])) in
  let body = list_mk_comb(ap,[app "f_ev_p3"; list_mk_comb(ap,[mid; app "f_ev_p1"])]) in
  list_mk_abs(args,body);;

let EM_ALLOWED = EM_ARGS @ [`i:num`; `f_ev_loop:int64->int64->int64->int64->int64->bool list->bool list->bool list->bool list->int64->int64->num->int64->int64->num->(uarch_event)list`];;

let EM_ASSUME_LEMMAS_TAC l =
  ASSUME_CALLEE_SAFETY_TAILED_TAC l.labs "H_ABS" THEN
  MAP_EVERY (fun (k,th) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th ("H_S"^string_of_int k)) (zip (0--3) l.lscan) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC l.lgs01 "H_G01" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC l.lgs2 "H_G2" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC l.lgs3 "H_G3" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC l.lt0 "H_T0" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC l.lt1 "H_T1";;

(* the callees are assumed before CONCRETIZE_F_EVENTS_TAC: assumed later,
   the final CHOOSE fails as the events then contain their f_events *)
let EM_INTRO_TAC l =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] th) "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600 "H_PERM" THEN
  EM_ASSUME_LEMMAS_TAC l THEN
  CONCRETIZE_F_EVENTS_TAC EM_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `r0:int64`; `r1:int64`; `r2:int64`; `r3:int64`;
    `seed:int64`; `sd:num`; `n0:int64`; `n1:int64`; `n2:int64`; `n3:byte`; `guard:int64`;
    `canary:int64`; `fp:int64`; `fr:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE;
              fst EM_EXEC] THEN
  DISCH_THEN(fun th -> (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) th THEN
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)(REWRITE_RULE[NONOVERLAPPING_CLAUSES] th)) THEN
  MAP_EVERY (fun g -> REWRITE_TAC[SPECL [`pc:num`; g] WORD_ADD] THEN
                      RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; g] WORD_ADD]))
   [`got_stack_chk_guard:num`; `got_memset:num`];;

let EM_DECLASS_TAC =
  MAP_EVERY (fun (h,d) -> ABBREV_TAC(mk_eq(d,em_declass h))) (zip EM_NONCES EM_DS);;

let EM_STATES_TAC =
  MAP_EVERY (fun (h,sv) ->
    let t = vsubst [em_input h,`M:num`] `mld_keccak_absorb_once 136 0x1F 66 M` in
    ABBREV_TAC(mk_eq(sv,t)) THEN
    ASSUME_TAC(SYM(REWRITE_RULE[ASSUME(mk_eq(t,sv))]
                    (SPECL [`66`; em_input h] mld_shake256_stream))))
   (zip EM_NONCES EM_SVS);;

let EM_MINIMAL_TAC =
  let p = mk_abs(`n:num`,EM_DONE `n:num`) in
  let sumd = end_itlist (mk_binop `(+):num->num->num`)
              (map (fun d -> mk_comb(`LENGTH:bool list->num`,d)) EM_DS) in
  MP_TAC(BETA_RULE(fst(EQ_IMP_RULE(ISPEC p MINIMAL)))) THEN
  ANTS_TAC THENL
   [EXISTS_TAC sumd THEN REPEAT CONJ_TAC THEN
    W(fun (asl,w) ->
      let m = index (rand(rand(rand(rand w)))) EM_DS in
      let h = el m EM_NONCES and d = el m EM_DS in
      let tth = snd(find (fun (_,th) ->
              concl th = mk_comb(mk_comb(`mld_rej_eta_terminates`,EM_ETA), em_stream h)) asl)
      and ath = snd(find (fun (_,th) -> concl th = mk_eq(em_declass h,d)) asl) in
      MATCH_MP_TAC(REWRITE_RULE[ath]
        (MATCH_MP (REWRITE_RULE[IMP_CONJ] (SPEC EM_ETA MLD_POLY_UNIFORM_ETA_DONE)) tth)) THEN
      ARITH_TAC);
    ALL_TAC] THEN
  ABBREV_TAC(mk_eq(`k0:num`,mk_comb(`(minimal):(num->bool)->num`,p))) THEN
  STRIP_TAC;;

let EM_SEED_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes(seed,64)) s = sd`) (concl th)
    then MP_TAC(MATCH_MP (SPEC `4` MLD_READ_BYTES_CHUNKS)
                 (REWRITE_RULE[ARITH_RULE `64 = 16 * 4`] th)) THEN
         MP_TAC(ISPECL [`seed:int64`; `64`; `read memory (s0:armstate)`] READ_BYTES_BOUND) THEN
         REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; ASSUME(concl th)]
    else NO_TAC) THEN
  DISCH_TAC THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  REWRITE_TAC[EXP; DIV_1; WORD_ADD_0] THEN STRIP_TAC;;

let EM_EXT k = mk_comb(mk_comb(`word_add:int64->int64->int64`,`fr:int64`),
                      mk_comb(`word:num->int64`,mk_small_numeral(1136 + 96 * k)));;

let EM_EXTSEED_TAC sname m =
  let s = mk_var(sname,`:armstate`) in
  let a = EM_EXT m and h = el m EM_NONCES in
  let t64 = list_mk_comb(`read:((armstate,num)component)->armstate->num`,
             [mk_comb(mk_comb(`(:>):(armstate,int64->byte)component->
                       ((int64->byte),num)component->(armstate,num)component`,
                       `memory`),
                      mk_comb(`bytes:int64#num->((int64->byte),num)component`,
                              mk_pair(a,`64`))); s]) in
  SUBGOAL_THEN (mk_eq(t64,`sd:num`)) ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `64 = 16 * 4`] THEN
    MATCH_MP_TAC MLD_BYTES_OF_CHUNKS THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o check (fun th ->
        can (term_match [] `sd < 2 EXP n`) (concl th))) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      REWRITE_TAC[EXP; DIV_1; WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [a; `sd:num`; h; s] MLD_READ_BYTES66_NONCE8) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[SAMPLING_WORD_ZX_8];
    DISCH_TAC];;

(* ------------------------------------------------------------------------- *)
(* The assertions at the test (A1), in the loop (INV, after 1 + i blocks)     *)
(* and at the exit (A2): per polynomial the count, the flag count < 256, the  *)
(* coefficients so far and the state; the frame slots and registers.         *)
(* ------------------------------------------------------------------------- *)

let EM_POLY = EM_INST
 `read (R:(armstate,int64)component) s =
  word(MIN 256 (LENGTH(FILTER (\x:bool. x) (SUB_LIST(0,2 * (FIRST + 136 * i)) D)))) /\
  read (FL:(armstate,int64)component) s =
  (if MIN 256 (LENGTH(FILTER (\x:bool. x) (SUB_LIST(0,2 * (FIRST + 136 * i)) D))) < 256
   then word 1 else word 0) /\
  (!k. k < MIN 256 (LENGTH(FILTER (\x:bool. x) (SUB_LIST(0,2 * (FIRST + 136 * i)) D)))
       ==> read (memory :> bytes32(word_add vec (word(4 * k)))) s =
           EL k (mld_rej_eta_list ETA str (2 * (FIRST + 136 * i)))) /\
  read (memory :> bytes(st,200)) s = val(keccak_squeeze (NB + i) (S:1600 word))`;;

let EM_CTRS = EM_P.m_ctrs and EM_FLAGS = EM_P.m_flags;;

let EM_ST k = mk_comb(mk_comb(`word_add:int64->int64->int64`,`fr:int64`),
                      mk_comb(`word:num->int64`,mk_small_numeral(336 + 200 * k)));;

let EM_POLYS =
  flat(map (fun k ->
    conjuncts(vsubst [el k EM_CTRS,`R:(armstate,int64)component`; el k EM_FLAGS,`FL:(armstate,int64)component`;
                      el k EM_VECS,`vec:int64`; el k EM_DS,`D:bool list`;
                      em_stream (el k EM_NONCES),`str:num->byte`; EM_ST k,`st:int64`;
                      el k EM_SVS,`S:1600 word`] EM_POLY)) (0--3));;

let EM_FRAME = EM_P.m_frame;;

let EM_A1 =
  let t = vsubst [`0`,`i:num`] (list_mk_conj EM_POLYS) in
  let t' = rhs(concl(REWRITE_CONV[MULT_CLAUSES; ADD_CLAUSES] t)) in
  mk_abs(`s:armstate`, list_mk_conj(conjuncts t' @ conjuncts EM_FRAME @ EM_P.m_a1));;

let EM_INV =
  list_mk_abs([`i:num`; `s:armstate`],
    list_mk_conj(EM_POLYS @ conjuncts EM_FRAME @ EM_P.m_inv));;

let EM_A2 =
  let res h vec =
    vsubst [em_stream h,`str:num->byte`; vec,`vec:int64`]
     (EM_INST `!k. k < 256
          ==> read (memory :> bytes32(word_add vec (word(4 * k)))) s =
              EL k (mld_rej_eta_list ETA str (2 * (FIRST + 136 * k0)))`) in
  mk_abs(`s:armstate`,
    list_mk_conj(map2 res EM_NONCES EM_VECS @ conjuncts EM_FRAME));;

let EM_PCN off = mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral (EM_B + off));;

let EM_SP = `word_add fr (word 240):int64`;;

(* ------------------------------------------------------------------------- *)
(* P1: the seed copies, memset, the absorbing, the four permutes, the copy    *)
(* of the first blocks to the buffers and the first four scans.              *)
(* ------------------------------------------------------------------------- *)

let EM_WB_TAC k =
  let a = EM_ST k in
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && (try rand(lhand(lhs c)) = mk_comb(`bytes:int64#num->((int64->byte),num)component`, mk_pair(a,`200`)) with _ -> false)
    then ASSUME_TAC(REWRITE_RULE[GSYM READ_MEMORY_WBYTES_1600] th) else NO_TAC);;

let EM_PERM_TAC k sv n =
  ARM_STEPS_TAC EM_EXEC [n] THEN EM_WB_TAC k THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc EM_EXEC "H_PERM"
    [`read X0 s`; sv; `pc:num`; `read SP s`; `read X30 s`] EM_ALLOWED (n + 1) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ETA_SQ1; PC_SQ_SUC; READ_MEMORY_WBYTES_1600]);;

(* the second permute of the first pass (65): the state is keccak_squeeze 2 *)
let ETA_SQ2 = prove
 (`!S:1600 word. keccak_f1600 (keccak_squeeze 1 S) = keccak_squeeze 2 S`,
  REWRITE_TAC[PC_SQ_SUC; ARITH_RULE `1 + 1 = 2`]);;

(* the first round of permutes rewrites the assumed permute theorem with
   ETA_SQ1, so the second one returns keccak_squeeze 1 (keccak_squeeze 1 S) *)
let ETA_SQ11 = prove
 (`!S:1600 word. keccak_squeeze 1 (keccak_squeeze 1 S) = keccak_squeeze 2 S`,
  REWRITE_TAC[GSYM ETA_SQ1; ETA_SQ2]);;

let EM_PERM2_TAC k sv n =
  ARM_STEPS_TAC EM_EXEC [n] THEN EM_WB_TAC k THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc EM_EXEC "H_PERM"
    [`read X0 s`; sv; `pc:num`; `read SP s`; `read X30 s`] EM_ALLOWED (n + 1) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ETA_SQ2; ETA_SQ11; READ_MEMORY_WBYTES_1600]);;

let EM_LOAD_FACTS_TAC sname =
  MAP_EVERY (fun k -> PC_LOAD_FACTS_TAC (Printf.sprintf "word_add fr (word %d)" (336 + 200 * k)) sname
     [16,0;16,16;16,32;16,48;16,64;16,80;16,96;16,112;8,128]) (0--3);;

let EM_BUF k = 1520 + EM_P.m_bstride * k;;

let EM_CHAIN_TAC t sname =
  MAP_EVERY (fun k -> PC_CHAIN_GEN "fr" "fr" (EM_BUF k)
     (Printf.sprintf "val(keccak_squeeze %s S%d)" t k) sname
     [0,16;16,16;32,16;48,16;64,16;80,16;96,16;112,16;128,8]) (0--3);;

(* the second block of the first pass (65), at offset 136 of the buffers *)
let EM_CHAIN2_TAC sname =
  MAP_EVERY (fun k -> PC_CHAIN_GEN "fr" "fr" (EM_BUF k + 136)
     (Printf.sprintf "val(keccak_squeeze 2 S%d)" k) sname
     [0,16;16,16;32,16;48,16;64,16;80,16;96,16;112,16;128,8]) (0--3);;

(* buffer k holds block t of stream k, in the form the scan wants: the
   address word_add fr (word (240 + boff + j)) *)
let EM_BUF_TAC k t sname =
  let s = mk_var(sname,`:armstate`) in
  let a = mk_comb(mk_comb(`word_add:int64->int64->int64`,`fr:int64`),
                  mk_comb(`word:num->int64`,mk_small_numeral(EM_BUF k))) in
  let sv = el k EM_SVS in
  let th0 = CONV_RULE(LAND_CONV(REWRITE_CONV[ARITH_RULE `8 * 136 = 1088`; ADD_CLAUSES]))
              (SPECL [sv; t; a; s] ETA_BUF_BYTES) in
  let ante = lhand(concl th0) in
  let boff = EM_BUF k - 240 in
  let alt = ARITH_RULE(parse_term(Printf.sprintf "%d + j = 240 + %d + j" (EM_BUF k) boff)) in
  FIRST_ASSUM(fun th ->
    if concl th = ante then
      let th2 = REWRITE_RULE[PTR_ADD_G; MULT_CLAUSES; ADD_CLAUSES] (MP th0 th) in
      ASSUME_TAC(REWRITE_RULE[alt] th2)
    else NO_TAC);;

(* the same for the two blocks of the first pass (65) *)
let EM_BUF2_TAC k sname =
  let s = mk_var(sname,`:armstate`) in
  let sv = el k EM_SVS in
  let th0 = CONV_RULE(LAND_CONV(REWRITE_CONV[ARITH_RULE `8 * 136 = 1088`] THENC
                                DEPTH_CONV NUM_ADD_CONV))
              (SPECL [sv; `fr:int64`; mk_small_numeral(EM_BUF k); s] ETA_BUF2_BYTES) in
  let a1,a2 = dest_conj(lhand(concl th0)) in
  let boff = EM_BUF k - 240 in
  let alt = ARITH_RULE(parse_term(Printf.sprintf "%d + j = 240 + %d + j" (EM_BUF k) boff)) in
  W(fun (asl,w) ->
    let f a = snd(find (fun (_,th) -> concl th = a) asl) in
    ASSUME_TAC(REWRITE_RULE[alt] (MP th0 (CONJ (f a1) (f a2)))));;

let EM_STREAM_TAC =
  W(fun (asl,w) ->
    let eqs = mapfilter (fun (_,th) -> let c = concl th in
       if can (term_match [] `mld_keccak_squeeze_byte 136 S 136 = mld_shake256_stream 66 M`) c then th
       else failwith "") asl in
    RULE_ASSUM_TAC(fun th -> if is_forall(concl th) && can (find_term ((=) `bytes8`)) (concl th)
                             then REWRITE_RULE eqs th else th));;

let EM_K0_TAC k sname =
  let vec = el k EM_VECS and s = mk_var(sname,`:armstate`) in
  SUBGOAL_THEN (vsubst [vec,`vec:int64`; s,`s:armstate`]
    `!k. k < 0 ==> read (memory :> bytes32 (word_add vec (word (4 * k)))) s = word 0`)
   ASSUME_TAC THENL [REWRITE_TAC[LT]; ALL_TAC];;

let EM_CNV m (asl,w) =
  let h = el m EM_NONCES and d = el m EM_DS in
  let tth = snd(find (fun (_,th) ->
              concl th = mk_comb(mk_comb(`mld_rej_eta_terminates`,EM_ETA), em_stream h)) asl)
  and ath = snd(find (fun (_,th) -> concl th = mk_eq(em_declass h,d)) asl) in
  REWRITE_RULE[ath] (MATCH_MP (SPEC EM_ETA MLD_POLY_UNIFORM_ETA_COUNT) tth);;

let EM_FIX0_TAC m =
  let h = el m EM_NONCES and d = el m EM_DS in
  W(fun (asl,w) ->
    let tth = snd(find (fun (_,th) ->
                concl th = mk_comb(mk_comb(`mld_rej_eta_terminates`,EM_ETA), em_stream h)) asl)
    and ath = snd(find (fun (_,th) -> concl th = mk_eq(em_declass h,d)) asl) in
    let dth = REWRITE_RULE[ath] (SPEC (EM_INST `FIRST:num`) (MATCH_MP
                (SPEC EM_ETA MLD_POLY_UNIFORM_ETA_DECLASS_FIRST) tth))
    and cth = SYM(SPEC (EM_INST `2 * FIRST`) (EM_CNV m (asl,w))) in
    RULE_ASSUM_TAC(REWRITE_RULE[dth; MLD_REJ_ETA_CTR_FIRST; cth; LT; SUB_0]));;

let EM_SCAN0_TAC k sname n =
  (if EM_P.m_first = 136 then EM_BUF_TAC k `0` sname else EM_BUF2_TAC k sname) THEN EM_STREAM_TAC THEN EM_K0_TAC k sname THEN
  ETA_CALL_TAC EM_EXEC ("H_S"^string_of_int k)
    [el k EM_VECS; EM_SP; `0`; `\k:num. word 0:int32`; em_stream (el k EM_NONCES); `pc:num`]
    EM_ALLOWED n THEN
  EM_FIX0_TAC k;;

let EM_P1_2_TAC =
  FULL_INIT_TAC THEN EM_SEED_TAC THEN
  ARM_STEPS_TAC EM_EXEC (1--3) THEN MLKEM_NATIVE_ADRP_TAC THEN ARM_STEPS_TAC EM_EXEC (4--33) THEN
  MAP_EVERY (fun k -> ARM_STEPS_TAC EM_EXEC [k]) (34--38) THEN LIBC_PLT_TAC EM_EXEC 38 THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" EM_EXEC [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] (ref EM_ALLOWED) 43 THEN
  MEMSET_ZERO_BYTES_TAC THEN
  MAP_EVERY (EM_EXTSEED_TAC "s43") (0--3) THEN
  ETA_CALL_TAC EM_EXEC "H_ABS" (EM_SP :: map em_input EM_NONCES @ [`pc:num`]) EM_ALLOWED 44 THEN
  EM_PERM_TAC 0 `S0:1600 word` 45 THEN ARM_STEPS_TAC EM_EXEC [47] THEN
  EM_PERM_TAC 1 `S1:1600 word` 48 THEN ARM_STEPS_TAC EM_EXEC [50] THEN
  EM_PERM_TAC 2 `S2:1600 word` 51 THEN ARM_STEPS_TAC EM_EXEC [53] THEN
  EM_PERM_TAC 3 `S3:1600 word` 54 THEN
  EM_LOAD_FACTS_TAC "s55" THEN ARM_STEPS_TAC EM_EXEC (56--123) THEN EM_CHAIN_TAC "1" "s123" THEN
  EM_SCAN0_TAC 0 "s123" 124 THEN
  ARM_STEPS_TAC EM_EXEC (125--130) THEN EM_SCAN0_TAC 1 "s130" 131 THEN
  ARM_STEPS_TAC EM_EXEC (132--135) THEN EM_SCAN0_TAC 2 "s135" 136 THEN
  ARM_STEPS_TAC EM_EXEC (137--140) THEN EM_SCAN0_TAC 3 "s140" 141 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* 65: two permutes and copies per state before the scans of 272 bytes *)
let EM_P1_4_TAC =
  FULL_INIT_TAC THEN EM_SEED_TAC THEN
  ARM_STEPS_TAC EM_EXEC (1--3) THEN MLKEM_NATIVE_ADRP_TAC THEN ARM_STEPS_TAC EM_EXEC (4--34) THEN
  MAP_EVERY (fun k -> ARM_STEPS_TAC EM_EXEC [k]) (35--39) THEN LIBC_PLT_TAC EM_EXEC 39 THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" EM_EXEC [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] (ref EM_ALLOWED) 44 THEN
  MEMSET_ZERO_BYTES_TAC THEN
  MAP_EVERY (EM_EXTSEED_TAC "s44") (0--3) THEN
  ETA_CALL_TAC EM_EXEC "H_ABS" (EM_SP :: map em_input EM_NONCES @ [`pc:num`]) EM_ALLOWED 45 THEN
  EM_PERM_TAC 0 `S0:1600 word` 46 THEN ARM_STEPS_TAC EM_EXEC [48] THEN
  EM_PERM_TAC 1 `S1:1600 word` 49 THEN ARM_STEPS_TAC EM_EXEC [51] THEN
  EM_PERM_TAC 2 `S2:1600 word` 52 THEN ARM_STEPS_TAC EM_EXEC [54] THEN
  EM_PERM_TAC 3 `S3:1600 word` 55 THEN
  EM_LOAD_FACTS_TAC "s56" THEN ARM_STEPS_TAC EM_EXEC (57--119) THEN EM_CHAIN_TAC "1" "s119" THEN
  EM_PERM2_TAC 0 `keccak_squeeze 1 S0` 120 THEN ARM_STEPS_TAC EM_EXEC [122] THEN
  EM_PERM2_TAC 1 `keccak_squeeze 1 S1` 123 THEN ARM_STEPS_TAC EM_EXEC [125] THEN
  EM_PERM2_TAC 2 `keccak_squeeze 1 S2` 126 THEN ARM_STEPS_TAC EM_EXEC [128] THEN
  EM_PERM2_TAC 3 `keccak_squeeze 1 S3` 129 THEN
  EM_LOAD_FACTS_TAC "s130" THEN ARM_STEPS_TAC EM_EXEC (131--182) THEN EM_CHAIN2_TAC "s182" THEN
  EM_SCAN0_TAC 0 "s182" 183 THEN
  ARM_STEPS_TAC EM_EXEC (184--189) THEN EM_SCAN0_TAC 1 "s189" 190 THEN
  ARM_STEPS_TAC EM_EXEC (191--194) THEN EM_SCAN0_TAC 2 "s194" 195 THEN
  ARM_STEPS_TAC EM_EXEC (196--199) THEN EM_SCAN0_TAC 3 "s199" 200 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let EM_P1_TAC = if EM_P.m_eta = 2 then EM_P1_2_TAC else EM_P1_4_TAC;;

let EM_CNT0 d = EM_INST `MIN 256 (LENGTH(FILTER (\x:bool. x) (SUB_LIST(0,2 * FIRST) D)))`
                |> vsubst [d,`D:bool list`];;

let EM_FORALL_TAC =
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) then
    MATCH_MP_TAC th THEN FIRST_ASSUM ACCEPT_TAC else NO_TAC);;

let EM_PC_RED_TAC =
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_eq c && (try rand(rator(lhs c)) = `PC` with Failure _ -> false) && is_cond(rhs c)
    then CONV_RULE(RAND_CONV(RATOR_CONV(LAND_CONV(DEPTH_CONV NUM_RED_CONV)) THENC
                            REWRITE_CONV[])) th
    else th);;

(* k0 = 0: the test exits at once *)

let EM_NOLOOP_TAC =
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES; ADD_CLAUSES]) THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
  MAP_EVERY (fun d ->
    SUBGOAL_THEN (mk_eq(EM_CNT0 d,`256`))
     (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[ARITH_RULE `MIN a b = a <=> a <= b`] THEN ASM_REWRITE_TAC[];
      ALL_TAC]) EM_DS THEN
  FULL_INIT_TAC THEN
  ETA_CALL_TAC EM_EXEC "H_T0" [`256`; `256`; `256`; `256`; `pc:num`] EM_ALLOWED 1 THEN
  EM_PC_RED_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(EM_FORALL_TAC THEN NO_TAC) THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* Entering the loop, its exit, and P3. The counts are abbreviated as c0..c3  *)
(* across region calls (ARM_SUBROUTINE_SIM_TAC cannot discharge c <= 256 for  *)
(* c = MIN 256 x) and unabbreviated after the last step; the events of the    *)
(* previous regions stay folded as e2.                                       *)
(* ------------------------------------------------------------------------- *)

let EM_MINIMALITY_TAC j =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Const("!",_),Abs(v,Comb(Comb(Const("==>",_),
        Comb(Comb(Const("<",_),v'),Var("k0",_))),_))) when v' = v ->
        MP_TAC(SPEC j th)
    | _ -> NO_TAC);;

let EM_MIN_LT = ARITH_RULE `!x. MIN 256 x < 256 <=> ~(256 <= x)`;;

let EM_CNT t d = vsubst [d,`D:bool list`; t,`t:num`]
  (EM_INST `MIN 256 (LENGTH(FILTER (\x:bool. x) (SUB_LIST(0,2 * (FIRST + 136 * t)) D)))`);;

let EM_SPINE t =
  let rec go t acc =
    match strip_comb t with
      (c,[a;b]) when (try fst(dest_const c) = "APPEND" with Failure _ -> false) -> go b (a::acc)
    | _ -> (rev acc, t) in
  go t [];;

let EM_SUFFIX_UNIFY_TAC (asl,w) =
  let l,r = dest_eq w in
  let li,lt = EM_SPINE l and ri,rt = EM_SPINE r in
  if lt <> rt then failwith "EM_SUFFIX_UNIFY_TAC: tails differ" else
  let rec common a b k = match a,b with
      x::a',y::b' when x = y -> common a' b' (k + 1) | _ -> k in
  let k = common (rev li) (rev ri) 0 in
  let ln = length li - k and rn = length ri - k in
  let ap = `APPEND:(uarch_event)list->(uarch_event)list->(uarch_event)list` in
  let mkapp xs tl = itlist (fun x t -> list_mk_comb(ap,[x;t])) xs tl in
  let suffix = mkapp (snd(chop_list ln li)) lt in
  let grp xs = end_itlist (fun x t -> list_mk_comb(ap,[x;t])) xs in
  let regroup side items n =
    if n = 0 then failwith "EM_SUFFIX_UNIFY_TAC: empty prefix" else
    let target = list_mk_comb(ap,[grp (fst(chop_list n items)); suffix]) in
    prove(mk_eq(side,target), REWRITE_TAC[APPEND_ASSOC]) in
  let lth = regroup l li ln and rth = regroup r ri rn in
  (GEN_REWRITE_TAC LAND_CONV [lth] THEN GEN_REWRITE_TAC RAND_CONV [rth] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[CONJUNCT1 ENUMERATEL; APPEND; APPEND_NIL] THEN
   UNIFY_F_EVENTS_TAC) (asl,w);;

let EM_DISCHARGE_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL
   [PURE_REWRITE_TAC[APPEND_NIL; CONJUNCT1 APPEND] THEN
    CONV_TAC(LAND_CONV(TRY_CONV CONS_TO_APPEND_CONV)) THEN
    (EM_SUFFIX_UNIFY_TAC ORELSE FULL_UNIFY_F_EVENTS_TAC); ALL_TAC] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND_NIL] THEN
  DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

(* the events of the previous regions stay folded as the variable e2 of the
   precondition, whose memaccess fact is an assumption *)
let EM_E2_FOLD_TAC =
  FIRST_ASSUM(fun mth ->
    match strip_comb (concl mth) with
      (k,[x;_;_]) when (try fst(dest_const k) = "memaccess_inbounds" with Failure _ -> false)
                       && is_var x ->
        FIRST_X_ASSUM(fun eth ->
          let c = concl eth in
          if is_eq c && lhs c = x then REWRITE_TAC[GSYM eth]
          else if is_eq c && rhs c = x then REWRITE_TAC[eth]
          else NO_TAC)
    | _ -> NO_TAC);;

let EM_E2_TAC tac = EM_E2_FOLD_TAC THEN tac;;

let EM_ALLOWED2 = EM_ALLOWED @ [`e2:(uarch_event)list`];;

let EM_IS_ABBREV tm =
  match tm with
    Comb(Comb(Const("=",_),Comb(Comb(Const("MIN",_),_),_)),Var(n,_)) ->
      String.length n = 2 && String.sub n 0 1 = "c"
  | _ -> false;;

(* abbreviate the counts terms ts as c0..c3, with MIN 256 x <= 256, the
   definitions packed into one assumption *)
let EM_ABBREV_TAC ts =
  MAP_EVERY (fun (m,t) ->
    ASSUME_TAC(SPECL [`256`; rand t] (ARITH_RULE `!a b. MIN a b <= a`)) THEN
    ABBREV_TAC(mk_eq(mk_var("c"^string_of_int m,`:num`),t))) (zip (0--3) ts) THEN
  (fun (asl,w) ->
    let hs,ks = partition (fun (_,th) -> EM_IS_ABBREV(concl th)) asl in
    let cth = end_itlist CONJ (map snd hs) in
    (null_meta,[("",ASSUME(concl cth))::ks,w],
     fun i ths -> PROVE_HYP (INSTANTIATE_ALL i cth) (hd ths)));;

let EM_UNABBREV_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_conj(concl th) && EM_IS_ABBREV(lhand(concl th))
    then MAP_EVERY (SUBST_ALL_TAC o SYM) (CONJUNCTS th) else NO_TAC);;

let EM_NOTDONE0 = mk_neg(rhs(concl(REWRITE_CONV[MULT_CLAUSES; ADD_CLAUSES] (EM_DONE `0`))));;

let EM_LOOP_INIT_TAC =
  FULL_INIT_TAC THEN EM_E2_TAC(
  SUBGOAL_THEN EM_NOTDONE0 ASSUME_TAC THENL
   [EM_MINIMALITY_TAC `0` THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `~(k0 = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN (list_mk_disj(map (fun t -> mk_binop `(<):num->num->bool` t `256`) (map EM_CNT0 EM_DS)))
   ASSUME_TAC THENL
   [REWRITE_TAC[EM_MIN_LT; GSYM DE_MORGAN_THM] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  EM_ABBREV_TAC (map EM_CNT0 EM_DS) THEN
  ETA_CALL_TAC EM_EXEC "H_T0" [`c0:num`; `c1:num`; `c2:num`; `c3:num`; `pc:num`] EM_ALLOWED2 1 THEN
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_eq c && (try rand(rator(lhs c)) = `PC` with Failure _ -> false) && is_cond(rhs c)
    then REWRITE_RULE[ASSUME `c0 < 256 \/ c1 < 256 \/ c2 < 256 \/ c3 < 256`] th
    else th) THEN
  ARM_STEPS_TAC EM_EXEC EM_P.m_init THEN
  ENSURES_FINAL_STATE_TAC THEN EM_UNABBREV_TAC THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
  EM_DISCHARGE_TAC);;

let EM_EXIT_TAC =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  MAP_EVERY (fun d ->
    SUBGOAL_THEN (mk_eq(EM_CNT `k0:num` d,`256`))
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC]) EM_DS THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let EM_RESULT = prove
 (EM_INST `!vec:int64 sd (h:byte) D k0 (s:armstate).
     mld_rej_eta_terminates ETA (mld_shake256_stream 66 (sd + 2 EXP 512 * val h))
     /\
     mld_poly_uniform_eta_declass ETA
      (mld_shake256_stream 66 (sd + 2 EXP 512 * val h)) = D /\
     256 <= LENGTH(FILTER (\x. x) (SUB_LIST(0,2 * (FIRST + 136 * k0)) D)) /\
     (!k. k < 256
          ==> read (memory :> bytes32(word_add vec (word(4 * k)))) s =
              EL k (mld_rej_eta_list ETA
                     (mld_shake256_stream 66 (sd + 2 EXP 512 * val h))
                     (2 * (FIRST + 136 * k0))))
     ==> (!k. k < 256
              ==> read (memory :> bytes32(word_add vec (word(4 * k)))) s =
                  mld_poly_uniform_eta ETA sd h k)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `D:bool list`)) THEN
  ASM_SIMP_TAC[mld_poly_uniform_eta] THEN
  MATCH_MP_TAC(REWRITE_RULE[ARITH_EQ; ARITH_RULE
    (EM_INST `2 * 136 * (NB + k) = 2 * (FIRST + 136 * k)`)]
   (SPEC EM_ETA MLD_REJ_ETA_POLY_EQ)) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPEC (EM_INST `2 * (FIRST + 136 * k0)`) o
    MATCH_MP (SPEC EM_ETA MLD_POLY_UNIFORM_ETA_COUNT)) THEN
  UNDISCH_TAC
   (EM_INST `256 <= LENGTH(FILTER (\x. x) (SUB_LIST(0,2 * (FIRST + 136 * k0))
     (mld_poly_uniform_eta_declass ETA
       (mld_shake256_stream 66 (sd + 2 EXP 512 * val(h:byte))))))`) THEN
  ARITH_TAC);;

let EM_RESULTS_TAC =
  MAP_EVERY (fun (h,(d,vec)) ->
    SUBGOAL_THEN
     (vsubst [h,`h:byte`; vec,`vec:int64`]
       (EM_INST `!k. k < 256
            ==> read (memory :> bytes32(word_add vec (word(4 * k)))) s0 =
                mld_poly_uniform_eta ETA sd h k`))
     ASSUME_TAC THENL
     [MATCH_MP_TAC EM_RESULT THEN
      MAP_EVERY EXISTS_TAC [d; `k0:num`] THEN ASM_REWRITE_TAC[];
      ALL_TAC])
   (zip EM_NONCES (zip EM_DS EM_VECS));;

let EM_P3_TAC =
  FULL_INIT_TAC THEN EM_E2_TAC(EM_RESULTS_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `k0:num`)) THEN
  ARM_STEPS_TAC EM_EXEC (1--5) THEN LIBC_PLT_TAC EM_EXEC 5 THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" EM_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] (ref EM_ALLOWED2) 10 THEN
  ARM_STEPS_TAC EM_EXEC (11--15) THEN LIBC_PLT_TAC EM_EXEC 15 THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" EM_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] (ref EM_ALLOWED2) 20 THEN
  ARM_STEPS_TAC EM_EXEC (21--42) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EM_DISCHARGE_TAC);;

(* ------------------------------------------------------------------------- *)
(* The loop body: four permutes, the copy of the next blocks, the guarded    *)
(* scans (GS01, GS2, GS3), the flags and the test (T1).                      *)
(* ------------------------------------------------------------------------- *)

let EM_CNTI d = EM_CNT `i:num` d;;

let EM_STI k = mk_comb(EM_INST `keccak_squeeze (NB + i)`, el k EM_SVS);;

(* fold the previous events of the body: the template's ENUMERATEL (i + 1)
   split and right-associated, the e2 equation of the invariant likewise *)
let EM_BODY_E2_TAC =
  REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  FIRST_ASSUM(fun mth ->
    match strip_comb (concl mth) with
      (k,[x;_;_]) when (try fst(dest_const k) = "memaccess_inbounds" with Failure _ -> false)
                       && is_var x ->
        FIRST_X_ASSUM(fun eth ->
          let c = concl eth in
          if is_eq c && lhs c = x
          then REWRITE_TAC[GSYM(REWRITE_RULE[GSYM APPEND_ASSOC] eth)] else NO_TAC)
    | _ -> NO_TAC);;

let EM_ALLOWED3 = EM_ALLOWED2 @ [`c0:num`; `c1:num`; `c2:num`; `c3:num`];;

let EM_PERM3_TAC k sv n =
  ARM_STEPS_TAC EM_EXEC [n] THEN EM_WB_TAC k THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc EM_EXEC "H_PERM"
    [`read X0 s`; sv; `pc:num`; `read SP s`; `read X30 s`] EM_ALLOWED3 (n + 1) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PC_SQ_SUC; READ_MEMORY_WBYTES_1600]);;

let EM_BODY_A_TAC =
  let p k = el k EM_P.m_body and sn n = "s"^string_of_int n in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  FULL_INIT_TAC THEN EM_BODY_E2_TAC THEN
  EM_ABBREV_TAC (map EM_CNTI EM_DS) THEN
  ARM_STEPS_TAC EM_EXEC (1--(p 0 - 1)) THEN RULE_ASSUM_TAC(REWRITE_RULE[ETA_CSET]) THEN
  EM_PERM3_TAC 0 (EM_STI 0) (p 0) THEN
  ARM_STEPS_TAC EM_EXEC ((p 0 + 2)--(p 1 - 1)) THEN EM_PERM3_TAC 1 (EM_STI 1) (p 1) THEN
  ARM_STEPS_TAC EM_EXEC ((p 1 + 2)--(p 2 - 1)) THEN EM_PERM3_TAC 2 (EM_STI 2) (p 2) THEN
  ARM_STEPS_TAC EM_EXEC ((p 2 + 2)--(p 3 - 1)) THEN EM_PERM3_TAC 3 (EM_STI 3) (p 3) THEN
  EM_LOAD_FACTS_TAC (sn (p 3 + 1)) THEN ARM_STEPS_TAC EM_EXEC ((p 3 + 2)--p 4) THEN
  EM_CHAIN_TAC (Printf.sprintf "((%d + i) + 1)" (EM_P.m_first / 136)) (sn (p 4)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ETA_CSET]) THEN
  MAP_EVERY (fun k -> EM_BUF_TAC k (EM_INST `NB + i`) (sn (p 4))) (0--3) THEN EM_STREAM_TAC THEN
  RULE_ASSUM_TAC(fun th -> if is_forall(concl th) && can (find_term ((=) `bytes8`)) (concl th)
     then REWRITE_RULE[ARITH_RULE(EM_INST `136 * (NB + i) + j = (FIRST + 136 * i) + j`)] th
     else th);;

let EM_BI k = mk_abs(`j:num`, mk_comb(em_stream (el k EM_NONCES), EM_INST `(FIRST + 136 * i) + j`));;

let EM_FI k = mk_abs(`k:num`, vsubst [em_stream (el k EM_NONCES),`str:num->byte`]
                (EM_INST `EL k (mld_rej_eta_list ETA str (2 * (FIRST + 136 * i)))`));;

let EM_CK k = mk_var("c"^string_of_int k,`:num`);;

let EM_CTRI k = list_mk_comb(`mld_rej_eta_ctr`,[EM_ETA; `256`; EM_CK k; EM_BI k; `136`]);;

let EM_ABBREV_EQ m (asl,w) =
  let c = EM_CK m in
  let pk = snd(find (fun (_,th) -> is_conj(concl th) && EM_IS_ABBREV(lhand(concl th))) asl) in
  find (fun th -> rhs(concl th) = c) (CONJUNCTS pk);;

let EM_BLOCK_THMS m (asl,w) =
  let h = el m EM_NONCES and d = el m EM_DS in
  let ath = EM_ABBREV_EQ m (asl,w) and cnv = EM_CNV m (asl,w) in
  let tth = snd(find (fun (_,th) ->
              concl th = mk_comb(mk_comb(`mld_rej_eta_terminates`,EM_ETA), em_stream h)) asl)
  and dath = snd(find (fun (_,th) -> concl th = mk_eq(em_declass h,d)) asl) in
  let sc = TRANS (SYM(SPEC (EM_INST `2 * (FIRST + 136 * i)`) cnv)) ath in
  let cth = REWRITE_RULE[ARITH_RULE(EM_INST `(FIRST + 136 * i) + 136 = FIRST + 136 * (i + 1)`);
                         GSYM(SPEC (EM_INST `2 * (FIRST + 136 * (i + 1))`) cnv)]
              (SPEC `136` (MATCH_MP (SPEC EM_ETA MLD_REJ_ETA_CTR_BLOCK) sc))
  and dth = REWRITE_RULE[dath]
              (SPEC `136` (MATCH_MP (SPEC EM_ETA MLD_POLY_UNIFORM_ETA_DECLASS_BLOCK) (CONJ tth sc))) in
  sc,cth,dth;;

let EM_DTH_TAC m = W(fun g -> let _,_,dth = EM_BLOCK_THMS m g in ASSUME_TAC dth);;

let EM_BODY_B_TAC =
  EM_DTH_TAC 0 THEN EM_DTH_TAC 1 THEN
  ETA_CALL_TAC EM_EXEC "H_G01"
    [`r0:int64`; `r1:int64`; EM_SP; `c0:num`; `c1:num`; EM_FI 0; EM_FI 1; EM_BI 0; EM_BI 1;
     `r2:int64`; `r3:int64`; `(if c2 < 256 then word 1 else word 0):int32`; `pc:num`]
    EM_ALLOWED3 (el 5 EM_P.m_body) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ETA_CSET]) THEN
  EM_DTH_TAC 2 THEN
  ETA_CALL_TAC EM_EXEC "H_G2" [`r2:int64`; EM_SP; `c2:num`; EM_FI 2; EM_BI 2; `pc:num`] EM_ALLOWED3
    (el 6 EM_P.m_body) THEN
  EM_DTH_TAC 3 THEN
  ETA_CALL_TAC EM_EXEC "H_G3" [`r3:int64`; EM_SP; `c3:num`; EM_FI 3; EM_BI 3; `pc:num`] EM_ALLOWED3
    (el 7 EM_P.m_body) THEN
  ETA_CALL_TAC EM_EXEC "H_T1" (map EM_CTRI (0--3) @ [`pc:num`]) EM_ALLOWED3 (el 8 EM_P.m_body);;

let EM_CTH_TAC =
  W(fun g ->
    let cths = map (fun m -> let _,cth,_ = EM_BLOCK_THMS m g in cth) (0--3) in
    RULE_ASSUM_TAC(REWRITE_RULE cths));;

(* the coefficients of polynomial m after the block *)
let EM_COEF_TAC m =
  let h = el m EM_NONCES and d = el m EM_DS and vec = el m EM_VECS in
  let strm = em_stream h in
  let goal = vsubst [vec,`vec:int64`; strm,`str:num->byte`; d,`D:bool list`]
   (EM_INST `!k. k < MIN 256 (LENGTH(FILTER (\x:bool. x)
                    (SUB_LIST(0,2 * (FIRST + 136 * (i + 1))) D)))
        ==> read (memory :> bytes32(word_add vec (word(4 * k)))) s =
            EL k (mld_rej_eta_list ETA str (2 * (FIRST + 136 * (i + 1))))`) in
  W(fun (asl,w) ->
    let sc,_,_ = EM_BLOCK_THMS m (asl,w) and cnv = EM_CNV m (asl,w) in
    let st = (let (_,th) = find (fun (_,th) -> try rand(rator(lhs(concl th))) = `PC` with _ -> false) asl in
              rand(lhs(concl th))) in
    let goal' = vsubst [st,`s:armstate`] goal in
    SUBGOAL_THEN goal' ASSUME_TAC THENL
     [X_GEN_TAC `k:num` THEN REWRITE_TAC[cnv] THEN DISCH_TAC THEN
      MP_TAC(SPECL [EM_ETA; strm; EM_INST `FIRST + 136 * i`; EM_CK m; `136`; `k:num`]
                   MLD_REJ_ETA_EL_BLOCK) THEN
      REWRITE_TAC[ARITH_RULE(EM_INST `(FIRST + 136 * i) + 136 = FIRST + 136 * (i + 1)`)] THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[sc]; DISCH_THEN SUBST1_TAC] THEN
      FIRST_ASSUM(fun th ->
        if is_forall(concl th) && free_in vec (concl th) && free_in st (concl th)
        then MP_TAC(SPEC `k:num` th) else NO_TAC) THEN
      REWRITE_TAC[cnv] THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[];
      ALL_TAC]);;

let EM_LS_TAC =
  SUBGOAL_THEN (mk_eq(EM_DONE `i + 1`,`~(i + 1 < k0)`))
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [EQ_TAC THENL
     [DISCH_THEN(fun dth -> DISCH_THEN(fun lth ->
        EM_MINIMALITY_TAC `i + 1` THEN REWRITE_TAC[dth; lth]));
      DISCH_TAC THEN SUBGOAL_THEN `i + 1 = k0` SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`i < k0`; `~(i + 1 < k0)`] THEN ARITH_TAC;
        REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC];;

(* memaccess of a long event list piece by piece: the previous events and
   the callee events from their facts, the rest concrete *)
let EM_MEM_PIECE_TAC (asl,w) =
  let piece = lhand(rator(rator w)) in
  let eqs = mapfilter (fun (_,th) -> let c = concl th in
     if is_eq c && is_var(lhs c) && rhs c = piece then th else failwith "") asl in
  let v = if eqs = [] then piece else lhs(concl(hd eqs)) in
  let mfs = mapfilter (fun (_,th) -> let c = concl th in
     match strip_comb c with
       (k,[x;_;_]) when (try fst(dest_const k) = "memaccess_inbounds" with _ -> false) && x = v -> th
     | _ -> failwith "") asl in
  if mfs = [] then failwith "EM_MEM_PIECE_TAC: no fact" else
  let mf = hd mfs in
  (REWRITE_TAC(map GSYM eqs) THEN MP_TAC mf THEN
   REWRITE_TAC[APPEND;APPEND_NIL] THEN
   ((MATCH_MP_TAC MEMACCESS_INBOUNDS_MEM THEN REWRITE_TAC[ALL;MEM] THEN NO_TAC) ORELSE
    (MATCH_MP_TAC MEMACCESS_INBOUNDS_CONTAINED THEN
     DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC THEN NO_TAC) ORELSE
    (DISCH_THEN ACCEPT_TAC))) (asl,w);;

let EM_MEMACCESS_TAC =
  REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         EM_MEM_PIECE_TAC;
         DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC THEN NO_TAC;
         DISCHARGE_MEMACCESS_INBOUNDS_TAC];;

let EM_DISCHARGE2_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL
   [PURE_REWRITE_TAC[APPEND_NIL; CONJUNCT1 APPEND] THEN
    CONV_TAC(LAND_CONV(TRY_CONV CONS_TO_APPEND_CONV)) THEN
    (EM_SUFFIX_UNIFY_TAC ORELSE FULL_UNIFY_F_EVENTS_TAC); ALL_TAC] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND_NIL] THEN EM_MEMACCESS_TAC;;

let EM_BODY_D_TAC =
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_eq c && (try rand(rator(lhs c)) = `PC` with Failure _ -> false) && is_cond(rhs c)
    then REWRITE_RULE[EM_MIN_LT; GSYM DE_MORGAN_THM] th else th) THEN
  EM_LS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE(EM_INST `(NB + i) + 1 = NB + (i + 1)`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN EM_UNABBREV_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  EM_DISCHARGE2_TAC;;

let EM_BODY_TAC =
  EM_BODY_A_TAC THEN EM_BODY_B_TAC THEN EM_CTH_TAC THEN
  MAP_EVERY EM_COEF_TAC (0--3) THEN EM_BODY_D_TAC;;

let EM_LOOP_TAC =
  REWRITE_TAC[EQF_INTRO(ASSUME `~(k0 = 0)`)] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `k0:num` (EM_PCN EM_P.m_ploop) (EM_PCN EM_P.m_pexit) EM_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; EM_LOOP_INIT_TAC; EM_BODY_TAC; EM_EXIT_TAC];;

let EM_MAIN_TAC =
  EM_INTRO_TAC EM_L THEN
  EM_DECLASS_TAC THEN EM_STATES_TAC THEN EM_MINIMAL_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC (EM_PCN EM_P.m_pexit) EM_A2 THEN CONJ_TAC THENL
   [ENSURES_EVENTS_SEQUENCE_TAC (EM_PCN EM_P.m_pt0) EM_A1 THEN CONJ_TAC THENL
     [EM_P1_TAC; ASM_CASES_TAC `k0 = 0` THENL [EM_NOLOOP_TAC; EM_LOOP_TAC]];
    EM_P3_TAC];;

(* ------------------------------------------------------------------------- *)
(* The whole function: the prologue realigns the stack pointer to 32 bytes   *)
(* (two cases: fr = stackpointer + 48 or + 32 after the offset of the stack  *)
(* pointer by the stack size), MAIN, the stack check and the epilogue.        *)
(* ------------------------------------------------------------------------- *)

let ETA_TOP_TEMPLATE = parse_term
 "\\(r0:int64) (r1:int64) (r2:int64) (r3:int64) (seed:int64) (dc0:bool list) (dc1:bool list) (dc2:bool list) (dc3:bool list) (guard:int64) (mf:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
    if aligned 32 stackpointer
    then f_ev_a r0 r1 r2 r3 seed dc0 dc1 dc2 dc3 guard mf pc stackpointer returnaddress
    else f_ev_u r0 r1 r2 r3 seed dc0 dc1 dc2 dc3 guard mf pc stackpointer returnaddress:(uarch_event)list";;

let ETA_TOP_ALLOWED =
  [`r0:int64`; `r1:int64`; `r2:int64`; `r3:int64`; `seed:int64`; `dc0:bool list`; `dc1:bool list`;
   `dc2:bool list`; `dc3:bool list`; `guard:int64`; `mf:int64`; `pc:num`; `stackpointer:int64`;
   `returnaddress:int64`];;

let ETA_TOP_PREFIX_TAC execth mainth =
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MP (SPECL [`mf:int64`;`ea:int64`;`el:num`;`ev:num`] mainth) th) "H_MAIN") THEN
  CONCRETIZE_F_EVENTS_TAC ETA_TOP_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; fst execth] THEN
  DISCH_THEN(fun th -> (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) th THEN
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)(REWRITE_RULE[NONOVERLAPPING_CLAUSES] th)) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC (vsubst [mk_small_numeral EM_P.m_stack,`n:num`]
                   `aligned 16 (word_add stackpointer (word n):int64)`) THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY (fun g -> REWRITE_TAC[SPECL [`pc:num`; g] WORD_ADD] THEN
                      RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; g] WORD_ADD]))
   [`got_stack_chk_guard:num`; `got_memset:num`] THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
                        (mk_const("X"^string_of_int n,[]))) ((19--28) @ [29]) THEN
  FULL_INIT_TAC;;

let ETA_ALIGN2048 = SAMPLING_ALIGN32_RULE 288;;

(* nonoverlapping facts for the call of MAIN, with fr = stackpointer + d;
   327672 and 327656 are the GOT entries of the stack guard and memset *)
let ETA_TOP_NOV d =
  let fr = Printf.sprintf "(word_add stackpointer (word %d):int64,%d)" d EM_P.m_frlen in
  let top = Printf.sprintf "(word_add stackpointer (word %d):int64,1)" EM_P.m_stack in
  let others = ["(seed:int64,64)"; top;
                "(word pc:int64,libmldsa_size)"; "(word_add (word pc) (word 327672):int64,8)";
                "(guard:int64,8)"; "(word_add (word pc) (word 327656):int64,8)"; "(ea:int64,el)"] in
  let rs = map (fun k -> Printf.sprintf "(r%d:int64,1024)" k) (0--3) in
  map (fun (a,b) -> parse_term(Printf.sprintf "nonoverlapping %s %s" a b))
   (map (fun r -> (r,fr)) rs @ map (fun x -> (fr,x)) others @
    allpairs (fun r x -> (r,x)) rs
     [top; "(word_add (word pc) (word 327672):int64,8)";
      "(word_add (word pc) (word 327656):int64,8)"]);;

let ETA_TOP_NOV_TAC d =
  MAP_EVERY (fun tm -> SUBGOAL_THEN tm (fun th -> ASSUME_TAC th THEN
                         ASSUME_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES] th)) THENL
                        [NONOVERLAPPING_TAC; ALL_TAC]) (ETA_TOP_NOV d);;

(* the simulator evaluates 2 EXP 512 in the events of MAIN: fold it back *)
let ETA_EXP512 = SYM(NUM_REDUCE_CONV `2 EXP 512`);;

(* the events unification abstracts over variables only: name the four
   declassified lists in the goal and in the events *)
let ETA_DECLASS_VARS_TAC =
  let is_ev th = let c = concl th in
    is_eq c && (try rand(rator(lhs c)) = `events` with Failure _ -> false) in
  FIRST_X_ASSUM(MP_TAC o check is_ev) THEN
  W(fun (_,w) ->
    let ts = setify(find_terms (fun t -> try fst(dest_const(fst(strip_comb t))) =
                                             "mld_poly_uniform_eta_declass" &&
                                           length(snd(strip_comb t)) = 2
                                       with Failure _ -> false) w) in
    MAP_EVERY (fun (k,t) -> ABBREV_TAC(mk_eq(mk_var("dcl"^string_of_int k,type_of t),t)))
      (zip (0--(length ts - 1)) ts)) THEN
  DISCH_TAC;;

let ETA_TOP_REST_TAC execth aligned =
  RULE_ASSUM_TAC(fun th ->
    if find_substring (string_of_term (concl th)) "18446744073709551584" <> None
    then REWRITE_RULE[] (REWRITE_RULE[MP (SPEC `stackpointer:int64` ETA_ALIGN2048)
                                          (ASSUME `aligned 16 (stackpointer:int64)`);
                                      if aligned then EQT_INTRO(ASSUME `aligned 32 (stackpointer:int64)`)
                                      else EQF_INTRO(ASSUME `~aligned 32 (stackpointer:int64)`)] th)
    else th) THEN
  (if aligned then
     SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 288):int64) /\
                   aligned 32 (word_add stackpointer (word 288):int64)` STRIP_ASSUME_TAC THENL
      [CONJ_TAC THEN CONV_TAC NORMALIZE_ALIGNED_WORD_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC]
   else
     MP_TAC(MATCH_MP PC_ALIGN272 (CONJ (ASSUME `aligned 16 (stackpointer:int64)`)
                                       (ASSUME `~aligned 32 (stackpointer:int64)`))) THEN STRIP_TAC) THEN
  ETA_TOP_NOV_TAC (if aligned then 48 else 32) THEN
  REMOVE_THEN "H_MAIN" (fun th -> ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
     (mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,execth,0x0,
      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,th)
     [`e:(uarch_event)list`; `r0:int64`; `r1:int64`; `r2:int64`; `r3:int64`; `seed:int64`; `sd:num`;
      `n0:int64`; `n1:int64`; `n2:int64`; `n3:byte`; `guard:int64`; `canary:int64`;
      `read X29 s`; `word_sub (read SP s) (word 240)`; `pc:num`] 10 THENL
     [(FULL_EXISTS_E2_TAC (ref ETA_TOP_ALLOWED) ORELSE PC_E2_TAC (ref ETA_TOP_ALLOWED));
      LABEL_TAC "H_MAIN" th]) THEN
  ARM_STEPS_TAC execth (11--11) THEN MLKEM_NATIVE_ADRP_TAC THEN ARM_STEPS_TAC execth (12--EM_P.m_nend) THEN
  ENSURES_FINAL_STATE_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[ETA_EXP512]) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ETA_DECLASS_VARS_TAC THEN PC_SAFETY_TAC;;

let ETA_TOP_CASE_TAC execth aligned =
  ARM_STEPS_TAC execth (1--9) THEN ETA_TOP_REST_TAC execth aligned;;

let ETA_TOP_TAC execth mainth =
  ETA_TOP_PREFIX_TAC execth mainth THEN
  ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [ETA_TOP_CASE_TAC execth true; ETA_TOP_CASE_TAC execth false];;

