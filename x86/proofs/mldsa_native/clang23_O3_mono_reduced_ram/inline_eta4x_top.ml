(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The proofs of mldsa{44,65,87}_poly_uniform_eta_4x of the clang 23 -O3     *)
(* monolithic reduced-RAM build, as one tactic for the three, with the       *)
(* parameters of each in a record pem: eta, the bytes t0 of the first pass   *)
(* (136, or 272 for eta = 4, two blocks), the buffers, the stack size, the   *)
(* labels, and the region lemmas of inline_eta4x.ml (ABS, SCAN, GUARD).      *)
(*                                                                           *)
(* The stages are those of the gcc 12 -O2 reduced-RAM proofs                 *)
(* (gcc12_O2_reduced_ram/poly_uniform_eta_4x_44_proof.ml), with the same     *)
(* invariant over the four polynomials and k0 the number of blocks after     *)
(* the first pass that the slowest of them needs:                            *)
(*                                                                           *)
(*  - PART1: the prologue (realigned to 32 bytes, rsp0 = bot + 296), the     *)
(*    four extended seeds (seed, nonce byte, zero byte) at rsp0 + 64 + 96k,  *)
(*    the memset of the four states, ABS, the permutations and the memcpys   *)
(*    of the first block (or two) of each stream to its buffer, and the      *)
(*    four scans (SCAN), which leave in R11, R10, R9 and CL the flags        *)
(*    whether each polynomial needs more;                                    *)
(*  - the test of the counts, which skips the loop if k0 = 0 (NOLOOP) or     *)
(*    enters it by one of four paths, depending on which polynomial is the   *)
(*    first that needs more (LOOP_INIT);                                     *)
(*  - the body of the outer loop (BODY): the flags stored to rsp0 + 28..31,  *)
(*    the four permutations and memcpys of the next block, the four guarded  *)
(*    scans (GUARD), the flags recomputed with SETB, and the test, again by  *)
(*    one of four paths, the last of which decides whether i + 1 < k0;       *)
(*  - PART3: three memsets (states, buffers, extended seeds), the epilogue   *)
(*    and the results from the invariant at k0 (PEM_RESULT).                 *)
(*                                                                           *)
(* The events of each iteration and of the entry depend on the path, i.e.    *)
(* on which counts are below 256, which the template states with             *)
(* conditionals on the declassified lists, and those of the guarded scans on *)
(* whether the count is below 256, as GUARD states them.                     *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_eta4x.ml";;
needs "x86/proofs/utils/mldsa_native_realign.ml";;

type pem = {
  pnn : string;               (* "44" *)
  pfn : string;               (* mldsa44_poly_uniform_eta_4x *)
  peta : int;
  pt0 : int;                  (* bytes of the first pass: 136 or 272 *)
  pbufs : int list;           (* the buffers, from rsp0 *)
  pstack : int;               (* 2295 *)
  pexec : thm * thm option array;
  pfull : term;               (* the FULL statement *)
  pabs : thm; pscans : thm list; pguards : thm list;
  pa1 : string; phead : string; pexit : string;
  pstreg : string list;       (* registers that hold the states after ABS *)
  pmset : int list            (* the sizes of the three memsets at the end *)
};;

let PEM_MC = mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc;;

(* ------------------------------------------------------------------------- *)
(* Terms: nonces, streams, counts, the template.                             *)
(* ------------------------------------------------------------------------- *)

let PEM_NONCES =
  [`word_zx(n0:int64):byte`; `word_zx(n1:int64):byte`;
   `word_zx(n2:int64):byte`; `word_zx(n3:int64):byte`]
and PEM_DS =
  [`dc0:bool list`; `dc1:bool list`; `dc2:bool list`; `dc3:bool list`]
and PEM_VECS = [`r0:int64`; `r1:int64`; `r2:int64`; `r3:int64`]
and PEM_SVS =
  [`S0:1600 word`; `S1:1600 word`; `S2:1600 word`; `S3:1600 word`];;

let pem_input h = vsubst [h,`h:byte`] `sd + 2 EXP 512 * val(h:byte)`;;
let pem_stream h = mk_comb(`mld_shake256_stream 66`,pem_input h);;
let pem_declass p h =
  mk_comb(mk_comb(`mld_poly_uniform_eta_declass`,mk_small_numeral p.peta),pem_stream h);;

let pem_groups p t =
  mk_binop `(+):num->num->num` (mk_small_numeral p.pt0)
   (mk_binop `( * ):num->num->num` `136` t);;

let PEM_ZERO_RULES =
  [MULT_CLAUSES; ADD_CLAUSES; ARITH_RULE `2 * 136 = 272`; ARITH_RULE `2 * 272 = 544`];;
let PEM_ZERO_CONV = REWRITE_CONV PEM_ZERO_RULES;;
let pem_z t = rhs(concl(PEM_ZERO_CONV t));;

let pem_count p d t =
  vsubst [d,`D:bool list`; pem_groups p t,`n:num`]
   `MIN 256 (LENGTH(FILTER (\x:bool. x) (SUB_LIST(0,2 * n) D)))`;;

let PEM_DONE1 p d n =
  vsubst [d,`D:bool list`; pem_groups p n,`n:num`]
   `256 <= LENGTH(FILTER (\x:bool. x) (SUB_LIST(0,2 * n) D))`;;

let PEM_DONE p n = list_mk_conj(map (fun d -> PEM_DONE1 p d n) PEM_DS);;

let PEM_ARGS =
  [`r0:int64`; `r1:int64`; `r2:int64`; `r3:int64`; `seed:int64`;
   `dc0:bool list`; `dc1:bool list`; `dc2:bool list`; `dc3:bool list`;
   `mf:int64`; `mc:int64`; `pc:num`; `stackpointer:int64`; `returnaddress:int64`];;

(* the path of the test of the counts: which of polynomials 0, 1, 2 is the
   first that needs more, or none of them *)
let pem_paths p n mk =
  let d k = PEM_DONE1 p (el k PEM_DS) n in
  mk_cond(mk_neg(d 0),mk 0,mk_cond(mk_neg(d 1),mk 1,mk_cond(mk_neg(d 2),mk 2,mk 3)));;

let PEM_TEMPLATE p =
  let args = PEM_ARGS in
  let fty = itlist (fun a t -> mk_fun_ty (type_of a) t) args `:(uarch_event)list` in
  let app n = list_mk_comb(mk_var(n,fty),args) in
  let k0 = mk_comb(`(minimal):(num->bool)->num`, mk_abs(`n:num`,PEM_DONE p `n:num`)) in
  let fl n = list_mk_comb(mk_var(n,
               itlist (fun a t -> mk_fun_ty (type_of a) t) args
                      (mk_fun_ty `:num` `:(uarch_event)list`)),args) in
  let loop = mk_abs(`i:num`,
               pem_paths p `i + 1` (fun k -> mk_comb(fl ("f_ev_loop"^string_of_int k),`i:num`))) in
  let enter = pem_z (pem_paths p `0` (fun k -> app ("f_ev_enter"^string_of_int k))) in
  let ap = `APPEND:(uarch_event)list->(uarch_event)list->(uarch_event)list` in
  let enum = list_mk_comb(`ENUMERATEL:num->(num->(uarch_event)list)->
                                     (uarch_event)list`,[k0;loop]) in
  let mid = mk_cond(mk_eq(k0,`0`),app "f_ev_skip",
              list_mk_comb(ap,[app "f_ev_exit";
                list_mk_comb(ap,[enum; enter])])) in
  let body = list_mk_comb(ap,[app "f_ev_p3";
               list_mk_comb(ap,[mid; app "f_ev_p1"])]) in
  list_mk_abs(args,body);;

let PEM_ALLOWED =
  PEM_ARGS @ [`bot:int64`; `i:num`; `c0:num`; `c1:num`; `c2:num`; `c3:num`];;

(* ------------------------------------------------------------------------- *)
(* Steps, calls of subroutines, region lemmas and libc functions, numbered   *)
(* by a counter.                                                             *)
(* ------------------------------------------------------------------------- *)

let pem_ctr = par_local_ref (fun () -> 0);;
let pem_exec = par_local_ref (fun () -> (TRUTH, [||]));;

let PEM_RESET : tactic = fun g -> pem_ctr () := 0; ALL_TAC g;;
let PEM_STEPS k : tactic = fun g ->
  let a = !(pem_ctr ()) + 1 and b = !(pem_ctr ()) + k in pem_ctr () := b; X86_STEPS_TAC (!(pem_exec ())) (a--b) g;;
let PEM_SSE_STEPS k : tactic = fun g ->
  let a = !(pem_ctr ()) + 1 and b = !(pem_ctr ()) + k in pem_ctr () := b; VERIF_SSE_STEPS_TAC (!(pem_exec ())) (a--b) g;;
let pem_state () = mk_var("s" ^ string_of_int !(pem_ctr ()),`:x86state`);;

let PEM_SHIFT =
  let ev = `e:(uarch_event)list` in
  let app_nil = prove(`!l:(uarch_event)list. l = APPEND [] l`, REWRITE_TAC[APPEND]) in
  let app_cons = CONJUNCT2 APPEND in
  let rec shift tm =
    if tm = ev then SPEC ev app_nil
    else match tm with
      Comb(Comb(Const("CONS",_),x),t) ->
        let th = shift t in
        let t0 = lhand(rand(concl th)) in
        let ev' = rand(rand(concl th)) in
        TRANS (AP_TERM (mk_comb(rator(rator tm),x)) th)
              (SYM (SPECL [x; t0; ev'] app_cons))
    | Comb(Comb(Const("APPEND",_),a),t) ->
        let th = shift t in
        let t0 = lhand(rand(concl th)) in
        TRANS (AP_TERM (rator tm) th)
              (SPECL [a; t0; ev] APPEND_ASSOC)
    | _ -> failwith ("PEM_SHIFT: " ^ string_of_term tm) in
  shift;;

let PEM_EXISTS_E2_TAC : tactic =
  FULL_EXISTS_E2_TAC (ref PEM_ALLOWED) ORELSE
  (W(fun (asl,w) ->
     let l = lhand w in
     let th = PEM_SHIFT l in
     REWRITE_TAC[th] THEN
     SAFE_UNIFY_REFL_TAC (ref PEM_ALLOWED) (ref ["f_events_callee"; "f_ev_"])));;

let PEM_CALL name ilist : tactic = fun g -> let n = !(pem_ctr ()) + 1 in pem_ctr () := n;
  (REMOVE_THEN name (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (PEM_MC,!(pem_exec ()),0x0,PEM_MC,th)
      (`e:(uarch_event)list`::(ilist @ [`pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`])) n THENL
     [PEM_EXISTS_E2_TAC; LABEL_TAC name th])) g;;

let PEM_REGION name ilist : tactic = fun g -> let n = !(pem_ctr ()) + 1 in pem_ctr () := n;
  (REMOVE_THEN name (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (PEM_MC,!(pem_exec ()),0x0,PEM_MC,th)
      (`e:(uarch_event)list`::ilist) n THENL
     [PEM_EXISTS_E2_TAC; LABEL_TAC name th])) g;;

let PEM_LIBC_CALL name f ilist : tactic = fun g ->
  let plt = layout ("plt_"^f) and got = layout ("got_"^f) in
  let n = !(pem_ctr ()) in
  pem_ctr () := n + 2;
  (LIBC_PLT_TAC (!(pem_exec ())) plt got n THEN
   REMOVE_THEN name (fun th ->
     LIBC_CONTRACT_SIM_TAC ~is_safety_thm:true (!(pem_exec ())) th
       (`e:(uarch_event)list`::(ilist @ [`read RSP s`; `read (memory :> bytes64 (read RSP s)) s`])) (n + 2) THENL
     [PEM_EXISTS_E2_TAC; LABEL_TAC name th]) THEN RSP_NORM_TAC) g;;

(* aligned 32 of bot + off, from the AND of the realignment *)
let PEM_ALIGNED32_TAC offs =
  let pat = `word_and (word_add stackpointer (word k)) (word 18446744073709551584):int64 = x` in
  FIRST_ASSUM(fun th ->
    if not (can (term_match [] pat) (concl th)) then NO_TAC else
    let ba = rhs(concl th) in
    let a = dest_small_numeral(rand(rand ba)) in
    let th32 = REWRITE_RULE[th] (SPEC (lhand(lhs(concl th))) REALIGN_ALIGNED_AND) in
    MAP_EVERY (fun off ->
      let d = mk_small_numeral(a - off) in
      let bo = subst [mk_small_numeral off,`n:num`] `word_add bot (word n):int64` in
      let sub = mk_comb(mk_comb(`word_sub:int64->int64->int64`,ba),
                        mk_comb(`word:num->int64`,d)) in
      let eq = WORD_RULE(mk_eq(bo,sub)) in
      let c = NORMALIZE_ALIGNED_WORD_CONV (mk_comb(`aligned 32:int64->bool`,sub)) in
      ASSUME_TAC(REWRITE_RULE[SYM eq] (EQ_MP (SYM c) th32))) offs);;

(* ------------------------------------------------------------------------- *)
(* The facts at the intermediate points (as in the gcc proofs): the frame,   *)
(* and for each polynomial its count (in R13, RBX, R14, R15), the flag of    *)
(* whether it needs more (R11, R10, R9, RCX: the low byte), its coefficients *)
(* so far and its state.                                                     *)
(* ------------------------------------------------------------------------- *)

let PEM_ST m = subst [mk_small_numeral(744 + 200 * m),`n:num`] `word_add bot (word n):int64`;;
let PEM_EXT m = subst [mk_small_numeral(360 + 96 * m),`n:num`] `word_add bot (word n):int64`;;
let PEM_BUF p m = subst [mk_small_numeral(296 + el m p.pbufs),`n:num`] `word_add bot (word n):int64`;;

let PEM_FRAME p =
  let n = p.pstack in
  parse_term(subst_tokens
   ["@RBP@",string_of_int(n-8); "@RBX@",string_of_int(n-48); "@R12@",string_of_int(n-40);
    "@R13@",string_of_int(n-32); "@R14@",string_of_int(n-24); "@R15@",string_of_int(n-16);
    "@RET@",string_of_int n]
 "read RSP s = word_add bot (word 296) /\\
  read RBP s = word_add stackpointer (word @RBP@) /\\
  read (memory :> bytes64 (word_add stackpointer (word @RBX@))) s = rbx_init /\\
  read (memory :> bytes64 (word_add stackpointer (word @R12@))) s = r12_init /\\
  read (memory :> bytes64 (word_add stackpointer (word @R13@))) s = r13_init /\\
  read (memory :> bytes64 (word_add stackpointer (word @R14@))) s = r14_init /\\
  read (memory :> bytes64 (word_add stackpointer (word @R15@))) s = r15_init /\\
  read (memory :> bytes64 (word_add stackpointer (word @RBP@))) s = rbp_init /\\
  read (memory :> bytes64 (word_add stackpointer (word @RET@))) s = returnaddress /\\
  read (memory :> bytes64 (word_add bot (word 352))) s = r0 /\\
  read (memory :> bytes64 (word_add bot (word 328))) s = r1 /\\
  read (memory :> bytes64 (word_add bot (word 336))) s = r2 /\\
  read (memory :> bytes64 (word_add bot (word 344))) s = r3 /\\
  ~read DF s /\\
  read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
  read (memory :> bytes(ea,el)) s = ev");;

let PEM_POLY p =
  vsubst [mk_small_numeral p.pt0,`t0:num`; mk_small_numeral p.peta,`eta:num`;
          mk_small_numeral (p.pt0 / 136),`nb:num`]
 `read (R:(x86state,int64)component) s =
  word(MIN 256 (LENGTH(FILTER (\x:bool. x)
                        (SUB_LIST(0,2 * (t0 + 136 * i)) D)))) /\
  word_zx(read (FL:(x86state,int64)component) s):byte =
  (if MIN 256 (LENGTH(FILTER (\x:bool. x)
                        (SUB_LIST(0,2 * (t0 + 136 * i)) D))) < 256
   then word 1 else word 0) /\
  (!k. k < MIN 256 (LENGTH(FILTER (\x:bool. x)
                            (SUB_LIST(0,2 * (t0 + 136 * i)) D)))
       ==> read (memory :> bytes32(word_add vec (word(4 * k)))) s =
           EL k (mld_rej_eta_list eta str (2 * (t0 + 136 * i)))) /\
  read (memory :> bytes(st,200)) s =
  val(keccak_squeeze (nb + i) (S:1600 word))`;;

let PEM_CREGS = [`R13`; `RBX`; `R14`; `R15`] and PEM_FREGS = [`R11`; `R10`; `R9`; `RCX`];;

let PEM_POLYS p =
  flat
   (map (fun (r,(f,(vec,(h,(d,(st,sv)))))) ->
          conjuncts
           (vsubst [r,`R:(x86state,int64)component`; f,`FL:(x86state,int64)component`;
                    vec,`vec:int64`; d,`D:bool list`; pem_stream h,`str:num->byte`;
                    st,`st:int64`; sv,`S:1600 word`]
                   (PEM_POLY p)))
        (zip PEM_CREGS (zip PEM_FREGS (zip PEM_VECS (zip PEM_NONCES
           (zip PEM_DS (zip (map PEM_ST (0--3)) PEM_SVS)))))));;

let PEM_INV p =
  list_mk_abs([`i:num`; `s:x86state`],
    list_mk_conj(PEM_POLYS p @ conjuncts (PEM_FRAME p)));;

let PEM_A1 p =
  let t = vsubst [`0`,`i:num`] (list_mk_conj(PEM_POLYS p)) in
  mk_abs(`s:x86state`, list_mk_conj(conjuncts (pem_z t) @ conjuncts (PEM_FRAME p)));;

let PEM_A2 p =
  let res h vec =
    vsubst [pem_stream h,`str:num->byte`; vec,`vec:int64`;
            mk_small_numeral p.pt0,`t0:num`; mk_small_numeral p.peta,`eta:num`]
     `!k. k < 256
          ==> read (memory :> bytes32(word_add vec (word(4 * k)))) s =
              EL k (mld_rej_eta_list eta str (2 * (t0 + 136 * k0)))` in
  mk_abs(`s:x86state`,
    list_mk_conj(map2 res PEM_NONCES PEM_VECS @ conjuncts (PEM_FRAME p)));;

(*** The result for one polynomial from the first t0 + 136 * k0 bytes ***)

let PEM_RESULT eta t0 =
  let et = mk_small_numeral eta and tt = mk_small_numeral t0 in
  let nb = if eta = 2 then 1 else 2 in
  prove
 (vsubst [et,`eta:num`; tt,`t0:num`]
  `!vec:int64 sd (h:byte) D k0 (s:x86state).
     mld_rej_eta_terminates eta (mld_shake256_stream 66 (sd + 2 EXP 512 * val h))
     /\
     mld_poly_uniform_eta_declass eta
      (mld_shake256_stream 66 (sd + 2 EXP 512 * val h)) = D /\
     256 <= LENGTH(FILTER (\x. x) (SUB_LIST(0,2 * (t0 + 136 * k0)) D)) /\
     (!k. k < 256
          ==> read (memory :> bytes32(word_add vec (word(4 * k)))) s =
              EL k (mld_rej_eta_list eta
                     (mld_shake256_stream 66 (sd + 2 EXP 512 * val h))
                     (2 * (t0 + 136 * k0))))
     ==> (!k. k < 256
              ==> read (memory :> bytes32(word_add vec (word(4 * k)))) s =
                  mld_poly_uniform_eta eta sd h k)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `D:bool list`)) THEN
  ASM_SIMP_TAC[mld_poly_uniform_eta] THEN
  MATCH_MP_TAC(REWRITE_RULE[ARITH_EQ; ARITH_RULE
    (vsubst [tt,`t0:num`; mk_small_numeral nb,`nb:num`]
     `2 * 136 * (nb + k) = 2 * (t0 + 136 * k)`)]
   (SPEC et MLD_REJ_ETA_POLY_EQ)) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPEC (vsubst [tt,`t0:num`] `2 * (t0 + 136 * k0)`) o
    MATCH_MP (SPEC et MLD_POLY_UNIFORM_ETA_COUNT)) THEN
  UNDISCH_TAC (vsubst [tt,`t0:num`; et,`eta:num`]
   `256 <= LENGTH(FILTER (\x. x) (SUB_LIST(0,2 * (t0 + 136 * k0))
     (mld_poly_uniform_eta_declass eta
       (mld_shake256_stream 66 (sd + 2 EXP 512 * val(h:byte))))))`) THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The setup: callee theorems and region lemmas, the template, the           *)
(* realigned frame (as in the gcc proofs, with N = stack and 48 bytes pushed *)
(* before the AND, so that rsp0 = bot + 296), the declassified lists, the    *)
(* absorbed states and k0.                                                   *)
(* ------------------------------------------------------------------------- *)

let PEM_INTRO_TAC p =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mcb = CONJ_PAIR th in
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] ms) "H_MEMSET" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memcpy_full_contract] mcb) "H_MEMCPY") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    (REWRITE_RULE[READ_MEMORY_WBYTES_1600]
      MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600) "H_PERM" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 p.pabs) "H_ABS" THEN
  MAP_EVERY (fun (k,th) -> ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 th) ("H_SCAN"^string_of_int k))
   (zip (0--3) p.pscans) THEN
  MAP_EVERY (fun (k,th) -> ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 th) ("H_GUARD"^string_of_int k))
   (zip (0--3) p.pguards) THEN
  CONCRETIZE_F_EVENTS_TAC (PEM_TEMPLATE p) THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst p.pexec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

let PEM_SETUP_TAC p =
  let n = p.pstack in
  let k = n - 48 in
  REALIGN_TAC k THEN REALIGN_FRAME_TAC n k THEN
  REALIGN_NONOV_TAC (k - 31)
   [`r0:int64,1024`; `r1:int64,1024`; `r2:int64,1024`; `r3:int64,1024`;
    `seed:int64,64`; `word pc:int64,libmldsa_size`;
    `word(pc + got_memset):int64,8`; `word(pc + got_memcpy):int64,8`;
    `ea:int64,el:num`;
    subst [mk_small_numeral k,`k:num`] `word_add stackpointer (word k):int64,48`;
    subst [mk_small_numeral n,`n:num`] `word_add stackpointer (word n):int64,32`] THEN
  REALIGN_ALIGNED_TAC (map (fun q -> 296 + 16 * q) (0--26)) THEN
  PEM_ALIGNED32_TAC [296] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15`;;

let PEM_DECLASS_TAC p =
  MAP_EVERY (fun (h,d) -> ABBREV_TAC(mk_eq(d,pem_declass p h)))
   (zip PEM_NONCES PEM_DS);;

let PEM_STATES_TAC =
  MAP_EVERY (fun (h,sv) ->
    let t = vsubst [pem_input h,`M:num`]
             `mld_keccak_absorb_once 136 0x1F 66 M` in
    ABBREV_TAC(mk_eq(sv,t)) THEN
    ASSUME_TAC(SYM(REWRITE_RULE[ASSUME(mk_eq(t,sv))]
                    (SPECL [`66`; pem_input h] mld_shake256_stream))))
   (zip PEM_NONCES PEM_SVS);;

let PEM_TERM p h =
  mk_comb(mk_comb(`mld_rej_eta_terminates`,mk_small_numeral p.peta),pem_stream h);;

(*** The count conversions for polynomial m, from its termination ***)

let PEM_CNV p m (asl,w) =
  let h = el m PEM_NONCES and d = el m PEM_DS in
  let tth = snd(find (fun (_,th) -> concl th = PEM_TERM p h) asl)
  and ath = snd(find (fun (_,th) -> concl th = mk_eq(pem_declass p h,d)) asl) in
  REWRITE_RULE[ath] (MATCH_MP (SPEC (mk_small_numeral p.peta) MLD_POLY_UNIFORM_ETA_COUNT) tth);;

let PEM_MINIMAL_TAC p =
  let pr = mk_abs(`n:num`,PEM_DONE p `n:num`) in
  let sumd = end_itlist (mk_binop `(+):num->num->num`)
              (map (fun d -> mk_comb(`LENGTH:bool list->num`,d)) PEM_DS) in
  MP_TAC(BETA_RULE(fst(EQ_IMP_RULE(ISPEC pr MINIMAL)))) THEN
  ANTS_TAC THENL
   [EXISTS_TAC sumd THEN REPEAT CONJ_TAC THEN
    W(fun (asl,w) ->
      let m = index (rand(rand(rand(rand w)))) PEM_DS in
      let h = el m PEM_NONCES and d = el m PEM_DS in
      let tth = snd(find (fun (_,th) -> concl th = PEM_TERM p h) asl)
      and ath = snd(find (fun (_,th) -> concl th = mk_eq(pem_declass p h,d)) asl) in
      MATCH_MP_TAC(REWRITE_RULE[ath]
        (MATCH_MP (REWRITE_RULE[IMP_CONJ] (SPEC (mk_small_numeral p.peta) MLD_POLY_UNIFORM_ETA_DONE))
                  tth)) THEN
      ARITH_TAC);
    ALL_TAC] THEN
  ABBREV_TAC(mk_eq(`k0:num`,mk_comb(`(minimal):(num->bool)->num`,pr))) THEN
  STRIP_TAC;;

let PEM_MINIMALITY_TAC j =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Const("!",_),Abs(v,Comb(Comb(Const("==>",_),
        Comb(Comb(Const("<",_),v'),Var("k0",_))),_))) when v' = v ->
        MP_TAC(SPEC j th)
    | _ -> NO_TAC);;

let PEM_DISCHARGE_TAC =
  REALIGN_UNBOT_TAC THEN SAMPLING_PATH_DISCHARGE_SPINE_TAC;;

(* ------------------------------------------------------------------------- *)
(* Lemmas for the first part.                                                *)
(* ------------------------------------------------------------------------- *)

(* the nonces on the stack as the bytes that the code loads *)
let PEM_READ_BYTES8_OF_64 = prove
 (`!a:int64 x s:x86state.
        read (memory :> bytes64 a) s = x
        ==> read (memory :> bytes8 a) s = word_zx x`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; BYTES64_WBYTES; BYTES8_WBYTES;
              READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              DIMINDEX_8; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  MP_TAC(SPECL [`a:int64`; `8`;
                `read (memory :> bytes(a:int64,8)) (s:x86state)`;
                `0`; `1`; `s:x86state`] READ_MEMORY_BYTES_SUB) THEN
  REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DIV_1]);;

let PEM_STACKARGS_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (term_match []
             `read (memory :> bytes64 (word_add stackpointer (word k))) s =
              (n:int64)`) (concl th) &&
       is_var(rand(concl th)) &&
       mem (name_of(rand(concl th))) ["n1"; "n2"; "n3"]
    then ASSUME_TAC(MATCH_MP PEM_READ_BYTES8_OF_64 th)
    else NO_TAC));;

(* zero bytes from the memset *)
let PEM_BYTES_ZERO = prove
 (`!a:int64 n s:x86state.
     (!i. i < n ==> read (memory :> bytes8 (word_add a (word i))) s = word 0)
     ==> read (memory :> bytes(a,n)) s = 0`,
  GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; ADD1; READ_MEMORY_BYTES_SNOC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num`) THEN
  REWRITE_TAC[ARITH_RULE `n < n + 1`] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let PEM_ZERO_TAC (a:term) n = fun g ->
  let st = pem_state () in
  (SUBGOAL_THEN (subst [a,`a:int64`; mk_small_numeral n,`n:num`; st,`s:x86state`]
                  `read (memory :> bytes(a:int64,n)) (s:x86state) = 0`) ASSUME_TAC THENL
   [MATCH_MP_TAC PEM_BYTES_ZERO THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    FIRST_ASSUM(fun th -> MATCH_ACCEPT_TAC(REWRITE_RULE[WORD_ZX_0] th));
    ALL_TAC]) g;;

(* the 136 bytes squeezed from a state K in a buffer *)
let PEM_FIRST136 = prove
 (`!(a:int64) (X:1600 word) s:x86state.
     read (memory :> bytes(a,200)) s = val X
     ==> read (memory :> bytes(a,136)) s = val X MOD 2 EXP (8 * 136)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; GSYM READ_BYTES_MOD] THEN
  REWRITE_TAC[READ_BYTES_MOD] THEN CONV_TAC NUM_REDUCE_CONV);;

let PEM_SQ_SUC = prove
 (`!(S:1600 word) i. keccak_f1600 (keccak_squeeze i S) = keccak_squeeze (i + 1) S`,
  REWRITE_TAC[GSYM ADD1; keccak_squeeze]);;

let PEM_SQ1 = prove
 (`!(S:1600 word). keccak_f1600 S = keccak_squeeze 1 S`,
  REWRITE_TAC[ARITH_RULE `1 = SUC 0`; keccak_squeeze]);;

let PEM_MOD_DIV = prove
 (`!x a b. b + 8 <= a ==> ((x MOD 2 EXP a) DIV 2 EXP b) MOD 256 = (x DIV 2 EXP b) MOD 256`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let PEM_SUBWORD8 = prove
 (`!(K:1600 word) j. word_subword K (8 * j,8):byte = word((val K DIV 2 EXP (8 * j)) MOD 256)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; VAL_WORD_SUBWORD; DIMINDEX_8] THEN
  REWRITE_TAC[ARITH_RULE `MIN 8 8 = 8`; ARITH_RULE `2 EXP 8 = 256`; MOD_MOD_REFL]);;

let PEM_BLOCK_BYTES = prove
 (`!(a:int64) (S:1600 word) t s:x86state.
     read (memory :> bytes(a,136)) s = val(keccak_squeeze (t + 1) S) MOD 2 EXP (8 * 136)
     ==> !j. j < 136
             ==> read (memory :> bytes8 (word_add a (word j))) s =
                 mld_keccak_squeeze_byte 136 S 136 (136 * t + j)`,
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP MLD_READ_BYTES_BYTES8) THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[mld_keccak_squeeze_byte] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `(136 + 136 * t + j) DIV 136 = t + 1 /\ (136 + 136 * t + j) MOD 136 = j`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `j:num`;
                    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `t + 1`] THEN
    UNDISCH_TAC `j < 136` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[PEM_SUBWORD8] THEN AP_TERM_TAC THEN MATCH_MP_TAC PEM_MOD_DIV THEN
  UNDISCH_TAC `j < 136` THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The first part, from the entry to the test before the outer loop (A1).    *)
(* ------------------------------------------------------------------------- *)

(* the seed as four 128-bit words, as in the gcc proof *)
let PEM_SEED_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes(seed,64)) s = sd`) (concl th)
    then MP_TAC(MATCH_MP (SPEC `4` MLD_READ_BYTES_CHUNKS)
                 (REWRITE_RULE[ARITH_RULE `64 = 16 * 4`] th)) THEN
         MP_TAC(ISPECL [`seed:int64`; `64`; `read memory (s0:x86state)`]
                       READ_BYTES_BOUND) THEN
         REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; ASSUME(concl th)]
    else NO_TAC) THEN
  DISCH_TAC THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  REWRITE_TAC[EXP; DIV_1; WORD_ADD_0] THEN STRIP_TAC;;

let PEM_NONCE_ZX = prove
 (`!x:byte. word_zx(word_zx(word_zx x:int32):int64):byte = x`,
  GEN_TAC THEN BITBLAST_TAC);;

(* the 66 bytes of extended seed m in state s, as in the gcc proof *)
let PEM_EXTSEED_TAC s m =
  let a = PEM_EXT m and h = el m PEM_NONCES in
  let t64 = subst [a,`a:int64`; s,`s:x86state`] `read (memory :> bytes(a,64)) s` in
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
    ASM_REWRITE_TAC[SAMPLING_WORD_ZX_8; PEM_NONCE_ZX] THEN NO_TAC;
    DISCH_TAC];;

(* the states after ABS as S0, ..., S3 *)
let PEM_ABSORBED_TAC =
  W(fun (asl,w) ->
    let abs = filter (fun th -> can (term_match []
                `mld_keccak_absorb_once r p n m = (S:1600 word)`) (concl th))
               (map snd asl) in
    RULE_ASSUM_TAC(fun th ->
      if can (term_match []
               `read (memory :> bytes(a,200)) s = val(x:1600 word)`)
             (concl th)
      then REWRITE_RULE abs th else th));;

(* the bytes of block t (0 for the first) of each stream in its buffer at
   rsp0 + bo, from the memcpy, as bytes of the streams, with the addresses
   in the form bot + (296 + bo + j) of the preconditions of the scans *)
let pem_block_raw asl st tt extra off =
  let sts = filter (fun th -> can (term_match []
              `mld_keccak_squeeze_byte 136 S 136 = mld_shake256_stream n m`)
              (concl th)) (map snd asl) in
  let a = subst [mk_small_numeral(296 + off),`n:num`] `word_add bot (word n):int64` in
  let pat = subst [st,`s:x86state`; a,`a:int64`]
    `read (memory :> bytes(a,136)) s = val(keccak_squeeze k (S:1600 word)) MOD 2 EXP (8 * 136)` in
  let th = snd(find (fun (_,th) -> can (term_match [] pat) (concl th)) asl) in
  let sv = rand(rand(lhand(rhs(concl th)))) in
  let lem = REWRITE_RULE[MULT_CLAUSES; ADD_CLAUSES; ARITH_RULE `1 + 1 = 2`]
             (SPECL [a; sv; tt; st] PEM_BLOCK_BYTES) in
  CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
   (REWRITE_RULE(sts @ extra) (MP lem th));;

let PEM_BLOCK_TAC p tt extra =
  W(fun (asl,w) ->
    let st = pem_state () in
    MAP_EVERY (fun bo ->
      let th1 = pem_block_raw asl st tt extra bo in
      let j,bd = dest_forall(concl th1) in
      let rhsj = rhs(rand bd) in
      let tm = subst [mk_small_numeral bo,`bo:num`; st,`s:x86state`; mk_abs(j,rhsj),`f:num->byte`]
        `!j. j < 136 ==> read (memory :> bytes8 (word_add bot (word (296 + bo + j)))) s = f j` in
      SUBGOAL_THEN (BETA_RULE(REFL tm) |> concl |> rhs) ASSUME_TAC THENL
       [REWRITE_TAC[ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
        MATCH_ACCEPT_TAC th1;
        ALL_TAC]) p.pbufs);;

(* two blocks, at bo and bo + 136, as the 272 bytes of the stream at bo      *)
let PEM_BLOCK2_TAC p =
  W(fun (asl,w) ->
    let st = pem_state () in
    MAP_EVERY (fun bo ->
      let th0 = pem_block_raw asl st `0` [] bo
      and th1 = pem_block_raw asl st `1` [] (bo + 136) in
      let j,bd = dest_forall(concl th0) in
      let strm = rator(rhs(rand bd)) in
      let tm = subst [mk_small_numeral bo,`bo:num`; st,`s:x86state`; strm,`f:num->byte`]
        `!j. j < 272 ==> read (memory :> bytes8 (word_add bot (word (296 + bo + j)))) s = f j` in
      let n0 = mk_small_numeral(296 + bo) and n1 = mk_small_numeral(296 + bo + 136) in
      SUBGOAL_THEN tm ASSUME_TAC THENL
       [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
        REWRITE_TAC[ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
        ASM_CASES_TAC `j < 136` THENL
         [MATCH_MP_TAC th0 THEN FIRST_ASSUM ACCEPT_TAC;
          MP_TAC(SPEC `j - 136` th1) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN (mk_conj(mk_eq(mk_binop `(+):num->num->num` n1 `j - 136`,
                                      mk_binop `(+):num->num->num` n0 `j:num`),
                                `136 + j - 136 = j`))
            ASSUME_TAC THENL [ASM_ARITH_TAC; POP_ASSUM(fun th -> REWRITE_TAC[th])]];
        ALL_TAC]) p.pbufs);;

(* rewrite the facts about the 200 bytes of the states only (not the
   assumed callee theorems) *)
let PEM_STATE_RULE_TAC ths =
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read (memory :> bytes(a,200)) s = val(x:1600 word)`) (concl th)
    then REWRITE_RULE ths th else th);;

let PEM_FIRST136_TAC : tactic = fun (asl,w) ->
  let st = pem_state () in
  let pat = subst [st,`s:x86state`] `read (memory :> bytes(a,200)) s = val(x:1600 word)` in
  MAP_EVERY (fun (_,th) ->
    if can (term_match [] pat) (concl th) then ASSUME_TAC(MATCH_MP PEM_FIRST136 th) else ALL_TAC) asl (asl,w);;

let PEM_FIRSTSCAN_TAC p m =
  let h = el m PEM_NONCES and d = el m PEM_DS and vec = el m PEM_VECS in
  let et = mk_small_numeral p.peta and tt = mk_small_numeral p.pt0 in
  PEM_REGION ("H_SCAN"^string_of_int m) [vec; `0`; pem_stream h; `pc:num`; `word_add bot (word 296):int64`] THEN
  W(fun (asl,w) ->
    let tth = snd(find (fun (_,th) -> concl th = PEM_TERM p h) asl)
    and ath = snd(find (fun (_,th) -> concl th = mk_eq(pem_declass p h,d)) asl) in
    let dth = REWRITE_RULE[ath] (SPEC tt (MATCH_MP
                (SPEC et MLD_POLY_UNIFORM_ETA_DECLASS_FIRST) tth))
    and cth = SYM(SPEC (mk_binop `( * ):num->num->num` `2` tt) (PEM_CNV p m (asl,w))) in
    RULE_ASSUM_TAC(REWRITE_RULE[dth; MLD_REJ_ETA_CTR_FIRST; cth; LE_0;
                                SUB_0; ARITH_RULE `2 * 136 = 272`; ARITH_RULE `2 * 272 = 544`]));;

let PEM_PART1_TAC p =
  let nb = p.pt0 / 136 in
  let x t k = mk_comb(mk_comb(`MOD`,mk_comb(`val:1600 word->num`,
              mk_comb(mk_comb(`keccak_squeeze`,mk_small_numeral t),el k PEM_SVS))),`2 EXP (8 * 136)`) in
  FULL_INIT_TAC THEN PEM_RESET THEN PEM_SEED_TAC THEN PEM_STACKARGS_TAC THEN
  SAMPLING_GHOST_REGS_TAC [`YMM0`; `YMM1`; `YMM2`; `YMM3`] "s0" THEN
  PEM_STEPS 8 THEN REALIGN_RSP_TAC THEN PEM_STEPS 54 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SAMPLING_SUBWORD_JOIN_128]) THEN
  SAMPLING_NONCE_BYTES_TAC THEN
  (fun g -> MAP_EVERY (PEM_EXTSEED_TAC (pem_state ())) (0--3) g) THEN
  PEM_LIBC_CALL "H_MEMSET" "memset" [`read RDI s`; `read RSI s`; `read RDX s`] THEN
  PEM_ZERO_TAC `word_add bot (word 744):int64` 800 THEN
  PEM_REGION "H_ABS" ([`word_add bot (word 296):int64`] @ map pem_input PEM_NONCES @ [`pc:num`]) THEN
  PEM_ABSORBED_TAC THEN
  MAP_EVERY (fun sv -> PEM_STEPS 2 THEN PEM_CALL "H_PERM" [`read RDI s`; sv]) PEM_SVS THEN
  PEM_STATE_RULE_TAC[PEM_SQ1] THEN PEM_FIRST136_TAC THEN
  MAP_EVERY (fun k -> PEM_STEPS 4 THEN
     PEM_LIBC_CALL "H_MEMCPY" "memcpy" [`read RDI s`; `read RSI s`; `read RDX s`; x 1 k]) (0--3) THEN
  (if nb = 1 then PEM_BLOCK_TAC p `0` [] else
   MAP_EVERY (fun sv -> PEM_STEPS 2 THEN
     PEM_CALL "H_PERM" [`read RDI s`; mk_comb(`keccak_squeeze 1`,sv)]) PEM_SVS THEN
   PEM_STATE_RULE_TAC[PEM_SQ_SUC; ARITH_RULE `1 + 1 = 2`] THEN PEM_FIRST136_TAC THEN
   MAP_EVERY (fun k -> PEM_STEPS 4 THEN
     PEM_LIBC_CALL "H_MEMCPY" "memcpy" [`read RDI s`; `read RSI s`; `read RDX s`; x 2 k]) (0--3) THEN
   PEM_BLOCK2_TAC p) THEN
  PEM_STEPS 2 THEN PEM_FIRSTSCAN_TAC p 0 THEN
  PEM_STEPS 6 THEN PEM_FIRSTSCAN_TAC p 1 THEN
  PEM_STEPS 3 THEN PEM_FIRSTSCAN_TAC p 2 THEN
  PEM_STEPS 3 THEN PEM_FIRSTSCAN_TAC p 3 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN PEM_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The tests of the counts: cmp r, 0x100; jb (and cmp r15d, 0xff; ja), with  *)
(* the counts c <= 256 (of the form MIN 256 x or with a fact c <= 256).      *)
(* ------------------------------------------------------------------------- *)

let PEM_VAL_ZX32 = prove
 (`!c. c <= 256 ==> val(word_zx(word c:int64):int32) = c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  SUBGOAL_THEN `c MOD 2 EXP 64 = c /\ c MOD 2 EXP 32 = c` (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN POP_ASSUM MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let PEM_JB256 = prove
 (`!c. c <= 256
       ==> (~(&(val(word_zx (word c:int64):int32)) - &256:int =
              &(val(word_sub (word_zx (word c:int64):int32) (word 256)))) <=> c < 256)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[PEM_VAL_ZX32] THEN
  REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_32] THEN
  ASM_SIMP_TAC[PEM_VAL_ZX32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  COND_CASES_TAC THENL
   [ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC(TAUT `~a /\ b ==> (~a <=> b)`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC(INT_ARITH `x < &256 /\ &0 <= y ==> ~(x - &256:int = y)`) THEN
      REWRITE_TAC[INT_POS; INT_OF_NUM_LT] THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC]]);;

let PEM_JA255 = prove
 (`!c. c <= 256
       ==> (~(~(&(val(word_zx (word c:int64):int32)) - &255:int =
                &(val(word_sub (word_zx (word c:int64):int32) (word 255)))) \/
              val(word_sub (word_zx (word c:int64):int32) (word 255)) = 0) <=>
            ~(c < 256))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `c:num` SAMPLING_CMP_255) THEN
  ANTS_TAC THENL [POP_ASSUM MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let PEM_MIN256 = prove(`!x. MIN 256 x <= 256`, ARITH_TAC);;
let PEM_MIN256_LT = prove(`!x. MIN 256 x < 256 <=> ~(256 <= x)`, ARITH_TAC);;

let PEM_CMP_CONV asl tm =
  let le c = if can (term_match [] `MIN 256 x`) c then SPEC (rand c) PEM_MIN256
             else snd(find (fun (_,th) -> concl th = mk_binop `(<=):num->num->bool` c `256`) asl) in
  match tm with
    Comb(Const("~",_),Comb(Comb(Const("=",_),Comb(Comb(Const("int_sub",_),Comb(Const("int_of_num",_),Comb(Const("val",_),Comb(Const("word_zx",_),Comb(Const("word",_),c))))),n)),_))
      when n = `&256:int` ->
      let th = MP (SPEC c PEM_JB256) (le c) in
      if lhs(concl th) = tm then th else failwith "PEM_CMP_CONV"
  | Comb(Const("~",_),Comb(Comb(Const("\\/",_),Comb(Const("~",_),Comb(Comb(Const("=",_),Comb(Comb(Const("int_sub",_),Comb(Const("int_of_num",_),Comb(Const("val",_),Comb(Const("word_zx",_),Comb(Const("word",_),c))))),n)),_))),_)) when n = `&255:int` ->
      let th = MP (SPEC c PEM_JA255) (le c) in
      if lhs(concl th) = tm then th else failwith "PEM_CMP_CONV"
  | _ -> failwith "PEM_CMP_CONV";;

(* decide the conditional RIP by the facts 256 <= x or ~(256 <= x) *)
let PEM_DECIDE_RIP_TAC : tactic = fun (asl,w) ->
  let facts = mapfilter (fun (_,th) -> let c = concl th in
     if can (term_match [] `256 <= x`) c then EQT_INTRO th
     else if is_neg c && can (term_match [] `256 <= x`) (rand c) then EQF_INTRO th else fail()) asl in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read RIP s = (if p then x else y)`) c then
      let th' = REWRITE_RULE (PEM_MIN256_LT::facts) (CONV_RULE(ONCE_DEPTH_CONV (PEM_CMP_CONV asl)) th) in
      if is_cond(rhs(concl th')) then failwith "PEM_DECIDE_RIP_TAC: undecided" else ASSUME_TAC th'
    else NO_TAC) (asl,w);;

(* rewrite the goal with the facts 256 <= x and ~(256 <= x) only, e.g. to
   decide the conditionals of the template *)
let PEM_CASE_REWRITE_TAC : tactic = fun (asl,w) ->
  let facts = flat(mapfilter (fun (_,th) -> let c = concl th in
     if can (term_match [] `256 <= x`) c then
       [EQT_INTRO th; EQF_INTRO(REWRITE_RULE[GSYM NOT_LT] th)]
     else if is_neg c && can (term_match [] `256 <= x`) (rand c) then
       [EQF_INTRO th; EQT_INTRO(REWRITE_RULE[NOT_LE] th)]
     else fail()) asl) in
  REWRITE_TAC facts (asl,w);;

(* the case facts also in the form x < 256 / ~(x < 256) in which the
   conditions of the template appear after ENUMERATEL_ADD1, for
   SAMPLING_SELECT_TAC *)
let PEM_CASE_BOTH_TAC : tactic = fun (asl,w) ->
  let facts = mapfilter (fun (_,th) -> let c = concl th in
     if can (term_match [] `256 <= x`) c then REWRITE_RULE[GSYM NOT_LT] th
     else if is_neg c && can (term_match [] `256 <= x`) (rand c) then REWRITE_RULE[NOT_LE] th
     else fail()) asl in
  MAP_EVERY ASSUME_TAC facts (asl,w);;

let PEM_TEST_STEPS n = PEM_STEPS 2 THEN PEM_DECIDE_RIP_TAC THEN
  (if n > 1 then PEM_STEPS 2 THEN PEM_DECIDE_RIP_TAC else ALL_TAC) THEN
  (if n > 2 then PEM_STEPS 2 THEN PEM_DECIDE_RIP_TAC else ALL_TAC) THEN
  (if n > 3 then PEM_STEPS 2 THEN PEM_DECIDE_RIP_TAC else ALL_TAC);;

(* ------------------------------------------------------------------------- *)
(* The branch round the loop when no more blocks are needed (k0 = 0), and    *)
(* the entry to the loop by one of the four paths of the test.               *)
(* ------------------------------------------------------------------------- *)

let PEM_NOLOOP_TAC p =
  let cs0 = map (fun d -> pem_z (pem_count p d `0`)) PEM_DS in
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE PEM_ZERO_RULES) THEN REWRITE_TAC[] THEN
  FULL_INIT_TAC THEN PEM_RESET THEN PEM_TEST_STEPS 4 THEN
  MAP_EVERY (fun c ->
    SUBGOAL_THEN (mk_eq(c,`256`))
     (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[ARITH_RULE `MIN a b = a <=> a <= b`] THEN ASM_REWRITE_TAC[];
      ALL_TAC]) cs0 THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC PEM_ZERO_RULES THEN ASM_REWRITE_TAC[] THEN
  PEM_DISCHARGE_TAC;;

let PEM_LOOP_INIT_TAC p =
  let d k = pem_z (PEM_DONE1 p (el k PEM_DS) `0`) in
  let fin = ENSURES_FINAL_STATE_TAC THEN
            REWRITE_TAC PEM_ZERO_RULES THEN PEM_CASE_REWRITE_TAC THEN ASM_REWRITE_TAC[] THEN
            PEM_DISCHARGE_TAC in
  FULL_INIT_TAC THEN
  ASM_CASES_TAC (d 0) THENL
   [ASM_CASES_TAC (d 1) THENL
     [ASM_CASES_TAC (d 2) THENL
       [SUBGOAL_THEN (mk_neg(d 3)) ASSUME_TAC THENL
         [PEM_MINIMALITY_TAC `0` THEN
          REWRITE_TAC PEM_ZERO_RULES THEN ASM_REWRITE_TAC[] THEN
          ANTS_TAC THENL [UNDISCH_TAC `~(k0 = 0)` THEN ARITH_TAC; REWRITE_TAC[]];
          ALL_TAC] THEN
        PEM_RESET THEN PEM_TEST_STEPS 4 THEN PEM_STEPS 1 THEN fin;
        PEM_RESET THEN PEM_TEST_STEPS 3 THEN fin];
      PEM_RESET THEN PEM_TEST_STEPS 2 THEN fin];
    PEM_RESET THEN PEM_TEST_STEPS 1 THEN fin];;

(* ------------------------------------------------------------------------- *)
(* The loop body, for iteration i, with the counts before it as c0, ..., c3  *)
(* (their definitions packed into one conjunction, as in the gcc proof).     *)
(* ------------------------------------------------------------------------- *)

let PEM_IS_ABBREV tm =
  match tm with
    Comb(Comb(Const("=",_),Comb(Comb(Const("MIN",_),_),_)),Var(n,_)) ->
      String.length n = 2 && String.sub n 0 1 = "c"
  | _ -> false;;

let PEM_ABBREV_TAC p =
  MAP_EVERY (fun m ->
    let t = pem_count p (el m PEM_DS) `i:num` in
    ASSUME_TAC(SPECL [`256`; rand t] (ARITH_RULE `!a b. MIN a b <= a`)) THEN
    ABBREV_TAC(mk_eq(mk_var("c"^string_of_int m,`:num`),t))) (0--3) THEN
  (fun (asl,w) ->
    let hs,ks = partition (fun (_,th) -> PEM_IS_ABBREV(concl th)) asl in
    let cth = end_itlist CONJ (map snd hs) in
    (null_meta,[("",ASSUME(concl cth))::ks,w],
     fun i ths -> PROVE_HYP (INSTANTIATE_ALL i cth) (hd ths)));;

let PEM_ABBREV p m =
  let eq = mk_eq(pem_count p (el m PEM_DS) `i:num`, mk_var("c"^string_of_int m,`:num`)) in
  fun (asl,w) ->
    tryfind (fun (_,th) -> find (fun th' -> concl th' = eq) (CONJUNCTS th)) asl;;

let PEM_UNABBREV_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_conj(concl th) && PEM_IS_ABBREV(lhand(concl th))
    then MAP_EVERY (SUBST_ALL_TAC o SYM) (CONJUNCTS th) else NO_TAC);;

(* the count, the declassified values and the coefficients after the guard
   of polynomial m, as ETA_4X_44_COMBINE_TAC of the gcc proof *)
let PEM_COMBINE_TAC p m =
  let h = el m PEM_NONCES and d = el m PEM_DS and vec = el m PEM_VECS in
  let et = mk_small_numeral p.peta in
  let c = mk_var("c"^string_of_int m,`:num`) in
  let strm = pem_stream h in
  let tg = pem_groups p `i:num` and tg1 = pem_groups p `i + 1` in
  let teq = ARITH_RULE(mk_eq(mk_binop `(+):num->num->num` tg `136`, tg1)) in
  let goal = vsubst [vec,`vec:int64`; strm,`str:num->byte`; d,`D:bool list`;
                     tg1,`t1:num`; et,`eta:num`]
   `!k. k < MIN 256 (LENGTH(FILTER (\x:bool. x) (SUB_LIST(0,2 * t1) D)))
        ==> read (memory :> bytes32(word_add vec (word(4 * k)))) s =
            EL k (mld_rej_eta_list eta str (2 * t1))` in
  W(fun gl ->
    let s = pem_state () in
    let goal = subst [s,`s:x86state`] goal in
    let isvecfact pat th =
      is_forall(concl th) && free_in vec (concl th) && free_in s (concl th) &&
      can (term_match [] pat) (concl th) in
    let ath = PEM_ABBREV p m gl and cnv = PEM_CNV p m gl in
    let tth = snd(find (fun (_,th) -> concl th = PEM_TERM p h) (fst gl))
    and dath = snd(find (fun (_,th) -> concl th = mk_eq(pem_declass p h,d)) (fst gl)) in
    let sc = TRANS (SYM(SPEC (mk_binop `( * ):num->num->num` `2` tg) cnv)) ath in
    let cth = REWRITE_RULE[teq; GSYM(SPEC (mk_binop `( * ):num->num->num` `2` tg1) cnv)]
               (SPEC `136` (MATCH_MP (SPEC et MLD_REJ_ETA_CTR_BLOCK) sc))
    and dth = REWRITE_RULE[dath]
               (SPEC `136` (MATCH_MP
                 (SPEC et MLD_POLY_UNIFORM_ETA_DECLASS_BLOCK)
                 (CONJ tth sc))) in
    RULE_ASSUM_TAC(REWRITE_RULE[cth; dth]) THEN
    SUBGOAL_THEN goal ASSUME_TAC THENL
     [X_GEN_TAC `k:num` THEN
      REWRITE_TAC[cnv] THEN DISCH_TAC THEN
      MP_TAC(SPECL [et; strm; tg; c; `136`; `k:num`] MLD_REJ_ETA_EL_BLOCK) THEN
      REWRITE_TAC[teq] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[sc]; DISCH_THEN SUBST1_TAC] THEN
      COND_CASES_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check
          (isvecfact `!k. k < c ==> P k`)) THEN
        ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o check
          (isvecfact `!k. c <= k /\ k < d ==> P k`)) THEN
        ASM_REWRITE_TAC[GSYM NOT_LT; cnv]];
      ALL_TAC]);;

let PEM_GUARD_TAC p m =
  let h = el m PEM_NONCES and vec = el m PEM_VECS in
  let c = mk_var("c"^string_of_int m,`:num`) in
  let b = mk_abs(`j:num`, mk_comb(pem_stream h, mk_binop `(+):num->num->num` (pem_groups p `i:num`) `j:num`)) in
  PEM_REGION ("H_GUARD"^string_of_int m)
   ([vec; c; b; `pc:num`; `word_add bot (word 296):int64`] @
    (if m = 0 then [`r1:int64`; `r2:int64`; `r3:int64`] else [])) THEN
  PEM_COMBINE_TAC p m;;

(* the flag facts word_zx(read F s0) = X in terms of the ghosts of F         *)
let PEM_FLAG_GHOST_TAC : tactic = fun (asl,w) ->
  let eqs = mapfilter (fun (_,th) -> let c = concl th in
    if can (term_match [] `read (FR:(x86state,int64)component) s0 = (v:int64)`) c && is_var(rhs c) &&
       mem (rand(lhand c)) PEM_FREGS then th else fail()) asl in
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `word_zx (read (FR:(x86state,int64)component) s0):byte = y`) (concl th)
                           then REWRITE_RULE eqs th else th) (asl,w);;

let PEM_BODY_A_TAC p =
  let nb = mk_small_numeral (p.pt0 / 136) in
  let nbi = mk_binop `(+):num->num->num` nb `i:num` in
  let sq k = mk_comb(mk_comb(`keccak_squeeze`,nbi),el k PEM_SVS) in
  let x k = mk_comb(mk_comb(`MOD`,mk_comb(`val:1600 word->num`,
              mk_comb(mk_comb(`keccak_squeeze`,mk_binop `(+):num->num->num` nbi `1`),el k PEM_SVS))),
              `2 EXP (8 * 136)`) in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  PEM_ABBREV_TAC p THEN FULL_INIT_TAC THEN PEM_RESET THEN
  SAMPLING_GHOST_REGS_TAC PEM_FREGS "s0" THEN PEM_FLAG_GHOST_TAC THEN
  PEM_STEPS 4 THEN
  (fun (asl,w) ->
    let fls = filter (fun (_,th) -> can (term_match [] `word_zx (x:int64):byte = y`) (concl th)) asl in
    RULE_ASSUM_TAC(fun th -> if can (term_match [] `read (memory :> bytes8 a) s = word (val (x:int64) MOD 256)`) (concl th)
                             then REWRITE_RULE(map snd fls) (REWRITE_RULE[KP_ZX_MOD8] th) else th) (asl,w)) THEN
  PEM_STEPS 2 THEN PEM_CALL "H_PERM" [`read RDI s`; sq 0] THEN
  PEM_STEPS 3 THEN PEM_CALL "H_PERM" [`read RDI s`; sq 1] THEN
  PEM_STEPS 2 THEN PEM_CALL "H_PERM" [`read RDI s`; sq 2] THEN
  PEM_STEPS 2 THEN PEM_CALL "H_PERM" [`read RDI s`; sq 3] THEN
  PEM_STATE_RULE_TAC[PEM_SQ_SUC] THEN PEM_FIRST136_TAC THEN
  MAP_EVERY (fun k -> PEM_STEPS 4 THEN
     PEM_LIBC_CALL "H_MEMCPY" "memcpy" [`read RDI s`; `read RSI s`; `read RDX s`; x k]) (0--3) THEN
  PEM_BLOCK_TAC p nbi [ARITH_RULE(subst [pem_groups p `i:num`,`t:num`; mk_small_numeral(p.pt0 / 136),`nb:num`]
                                       `136 * (nb + i) + j = t + j`)];;

(* the flags from SETB after the four guards *)
let PEM_ZX_JOIN8 = prove
 (`!(h:56 word) (l:byte). word_zx(word_join h l:int64):byte = l`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

let PEM_SETB_FLAGS_TAC : tactic = fun (asl,w) ->
  let st = pem_state () in
  MAP_EVERY (fun f ->
    let pat = subst [f,`FR:(x86state,int64)component`; st,`s:x86state`]
      `read (FR:(x86state,int64)component) (s:x86state) = word_join (h:56 word) (l:byte)` in
    match (try Some(find (fun (_,th) -> can (term_match [] pat) (concl th)) asl) with Failure _ -> None) with
      Some(_,th) ->
        let th1 = REWRITE_RULE[PEM_ZX_JOIN8] (AP_TERM `word_zx:int64->byte` th) in
        ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV (PEM_CMP_CONV asl)) th1)
    | None -> failwith ("PEM_SETB_FLAGS_TAC: "^string_of_term f)) PEM_FREGS (asl,w);;

(* the last test of the iteration, when polynomials 0 to 2 are complete: as
   ETA_4X_44_LAST_TAC of the gcc proof, the RIP as a function of i + 1 < k0 *)
let PEM_LAST_TAC p =
  let d k = PEM_DONE1 p (el k PEM_DS) `i + 1` in
  SUBGOAL_THEN (mk_eq(d 3, `~(i + 1 < k0)`)) (fun th ->
    FIRST_X_ASSUM(fun rth ->
      if can (term_match [] `read RIP s = (if p then x else y)`) (concl rth)
      then ASSUME_TAC(REWRITE_RULE[th] rth) else NO_TAC)) THENL
   [EQ_TAC THENL
     [DISCH_TAC THEN PEM_MINIMALITY_TAC `i + 1` THEN
      REWRITE_TAC(map (fun k -> ASSUME(d k)) (0--3));
      DISCH_TAC THEN SUBGOAL_THEN `i + 1 = k0` SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`i < k0`; `~(i + 1 < k0)`] THEN ARITH_TAC;
        FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC];;

let PEM_NOTLAST_TAC p m =
  let d k = PEM_DONE1 p (el k PEM_DS) `i + 1` in
  SUBGOAL_THEN `i + 1 < k0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `k0 = i + 1` SUBST_ALL_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`i < k0`; `k0 <= i + 1`] THEN ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC (mk_neg(d m)) THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let PEM_WORD_COND = prove
 (`!b x y. word (if b then x else y):int64 = if b then word x else word y`,
  MESON_TAC[]);;

let PEM_BODY_TEST_TAC p =
  let d k = PEM_DONE1 p (el k PEM_DS) `i + 1` in
  let fin = ENSURES_FINAL_STATE_TAC THEN
            REWRITE_TAC[PEM_WORD_COND;
              ARITH_RULE(subst [mk_small_numeral (p.pt0 / 136),`nb:num`] `nb + i + 1 = (nb + i) + 1`)] THEN
            PEM_CASE_REWRITE_TAC THEN
            ASM_REWRITE_TAC[] THEN
            PEM_UNABBREV_TAC THEN PEM_CASE_BOTH_TAC THEN PEM_DISCHARGE_TAC in
  let path n tac = (fun g -> pem_ctr () := n; ALL_TAC g) THEN tac THEN fin in
  (fun g -> SAMPLING_GHOST_REGS_TAC PEM_FREGS (fst(dest_var(pem_state ()))) g) THEN
  PEM_STEPS 9 THEN PEM_SETB_FLAGS_TAC THEN
  (fun g ->
    let n0 = !(pem_ctr ()) in
    (ASM_CASES_TAC (d 0) THENL
     [ASM_CASES_TAC (d 1) THENL
       [ASM_CASES_TAC (d 2) THENL
         [path n0 (PEM_DECIDE_RIP_TAC THEN PEM_STEPS 2 THEN PEM_DECIDE_RIP_TAC THEN
                   PEM_STEPS 2 THEN PEM_DECIDE_RIP_TAC THEN PEM_STEPS 2 THEN
                   FIRST_X_ASSUM(fun rth ->
                     if can (term_match [] `read RIP s = (if p then x else y)`) (concl rth)
                     then ASSUME_TAC(REWRITE_RULE[PEM_MIN256_LT]
                            (CONV_RULE(ONCE_DEPTH_CONV (PEM_CMP_CONV [])) rth)) else NO_TAC) THEN
                   PEM_LAST_TAC p);
          path n0 (PEM_NOTLAST_TAC p 2 THEN PEM_DECIDE_RIP_TAC THEN PEM_STEPS 2 THEN
                   PEM_DECIDE_RIP_TAC THEN PEM_STEPS 2 THEN PEM_DECIDE_RIP_TAC)];
        path n0 (PEM_NOTLAST_TAC p 1 THEN PEM_DECIDE_RIP_TAC THEN PEM_STEPS 2 THEN PEM_DECIDE_RIP_TAC)];
      path n0 (PEM_NOTLAST_TAC p 0 THEN PEM_DECIDE_RIP_TAC)]) g);;

let PEM_BODY_TAC p =
  PEM_BODY_A_TAC p THEN
  PEM_GUARD_TAC p 0 THEN PEM_GUARD_TAC p 1 THEN PEM_GUARD_TAC p 2 THEN PEM_GUARD_TAC p 3 THEN
  PEM_BODY_TEST_TAC p;;

(*** The exit of the loop, where all four have 256 coefficients ***)

let PEM_EXIT_TAC p =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  MAP_EVERY (fun d ->
    SUBGOAL_THEN (mk_eq(pem_count p d `k0:num`,`256`))
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC]) PEM_DS THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  PEM_DISCHARGE_TAC;;

let PEM_LOOP_TAC p =
  REWRITE_TAC[EQF_INTRO(ASSUME `~(k0 = 0)`)] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `k0:num`
   (parse_term("pc + " ^ p.pfn ^ "_" ^ p.phead)) (parse_term("pc + " ^ p.pfn ^ "_" ^ p.pexit)) (PEM_INV p) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(k0 = 0)` THEN ARITH_TAC;
    PEM_LOOP_INIT_TAC p;
    PEM_BODY_TAC p;
    PEM_EXIT_TAC p];;

(* ------------------------------------------------------------------------- *)
(* The events at the end of PART3: L = APPEND (f_ev_p3 args) R2, where the   *)
(* events L of the simulation end with those of the parts before (R2) but    *)
(* are associated differently (the calls of memset), so that                 *)
(* FULL_UNIFY_F_EVENTS_TAC does not find R2 in L: PEM_TAIL_UNIFY_TAC puts    *)
(* both into the normal form of APPEND, finds R2 at the end of L and unifies *)
(* f_ev_p3 with the events before it.                                        *)
(* ------------------------------------------------------------------------- *)

let PEM_APPEND_NORM = REWRITE_CONV[APPEND; APPEND_NIL; GSYM APPEND_ASSOC];;

let PEM_EVENTS_EVAL_CONV =
  PEM_APPEND_NORM THENC
  TOP_DEPTH_CONV(WORD_RED_CONV ORELSEC INT_RED_CONV ORELSEC NUM_RED_CONV) THENC
  REWRITE_CONV[];;

let PEM_TAIL_UNIFY_TAC : tactic = fun (asl,w) ->
  let l,r = dest_eq w in
  let r2 = rand r in
  let nl = rhs(concl(PEM_APPEND_NORM l)) and nr2 = rhs(concl(PEM_APPEND_NORM r2)) in
  let is_sp t = is_comb t && is_comb(rator t) && is_const(rator(rator t)) &&
                mem (fst(dest_const(rator(rator t)))) ["APPEND"; "CONS"] in
  let rec len t = if is_sp t then 1 + len (rand t) else 0 in
  let k = len nl - len nr2 in
  if k < 0 then failwith "PEM_TAIL_UNIFY_TAC: short" else
  let nil = `[]:(uarch_event)list` in
  let rec cut n t = if n = 0 then nil else mk_comb(rator t,cut (n - 1) (rand t)) in
  let x = cut k nl in
  let ap = rator(rator r) in
  (SUBGOAL_THEN (mk_eq(l,mk_comb(mk_comb(ap,x),r2))) SUBST1_TAC THENL
   [CONV_TAC(BINOP_CONV PEM_EVENTS_EVAL_CONV) THEN REFL_TAC; ALL_TAC] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN UNIFY_F_EVENTS_TAC) (asl,w);;

(* the events in goal and facts (memaccess facts, definitions of event
   lists) in one form, with ground words and numbers evaluated and APPEND
   right-associated everywhere, for SAMPLING_MEMACCESS_SPINE_TAC *)
let PEM_EVAL_EVENTS_TAC : tactic =
  let is_mi tm = is_comb tm && (try fst(dest_const(fst(strip_comb tm))) = "memaccess_inbounds"
                                with Failure _ -> false) in
  let evty = `:(uarch_event)list` in
  let conv = TOP_DEPTH_CONV(WORD_RED_CONV ORELSEC INT_RED_CONV ORELSEC NUM_RED_CONV) THENC
             REWRITE_CONV[] THENC PEM_APPEND_NORM in
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_mi c || (is_eq c && is_var(lhs c) && type_of(lhs c) = evty)
    then CONV_RULE conv th else th) THEN
  CONV_TAC conv;;

let PEM_PATH_DISCHARGE_TAIL_TAC =
  let beta_all =
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) in
  let has_const s tm =
    can (find_term (fun t -> is_const t && fst(dest_const t) = s)) tm in
  REWRITE_TAC[ENUMERATEL_ADD1] THEN beta_all THEN SAMPLING_SELECT_TAC THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC ORELSE PEM_TAIL_UNIFY_TAC; ALL_TAC] THEN
  beta_all THEN
  REWRITE_TAC[NOT_LT] THEN RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
  DISCARD_ASSUMPTIONS_TAC
   (fun th -> has_const "read" (concl th) || has_const "ensures" (concl th))
  THEN
  SAMPLING_ABBREV_DELTAS_TAC THEN PEM_EVAL_EVENTS_TAC THEN SAMPLING_MEMACCESS_SPINE_TAC;;

(* ------------------------------------------------------------------------- *)
(* Zeroing the state, the buffers and the extended seeds (three memsets) and *)
(* the return, with the polynomials as mld_poly_uniform_eta.                 *)
(* ------------------------------------------------------------------------- *)

let PEM_RESULTS_TAC p =
  let rth = PEM_RESULT p.peta p.pt0 in
  let et = mk_small_numeral p.peta in
  MAP_EVERY (fun (h,(d,vec)) ->
    SUBGOAL_THEN
     (vsubst [h,`h:byte`; vec,`vec:int64`; et,`eta:num`]
       `!k. k < 256
            ==> read (memory :> bytes32(word_add vec (word(4 * k)))) s0 =
                mld_poly_uniform_eta eta sd h k`)
     ASSUME_TAC THENL
     [MATCH_MP_TAC rth THEN
      MAP_EVERY EXISTS_TAC [d; `k0:num`] THEN ASM_REWRITE_TAC[];
      ALL_TAC])
   (zip PEM_NONCES (zip PEM_DS PEM_VECS));;

let PEM_PART3_TAC p =
  FULL_INIT_TAC THEN PEM_RESULTS_TAC p THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `k0:num`)) THEN
  PEM_RESET THEN
  PEM_STEPS 5 THEN PEM_LIBC_CALL "H_MEMSET" "memset" [`read RDI s`; `read RSI s`; `read RDX s`] THEN
  PEM_STEPS 5 THEN PEM_LIBC_CALL "H_MEMSET" "memset" [`read RDI s`; `read RSI s`; `read RDX s`] THEN
  PEM_STEPS 5 THEN PEM_LIBC_CALL "H_MEMSET" "memset" [`read RDI s`; `read RSI s`; `read RDX s`] THEN
  PEM_STEPS 17 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REALIGN_UNBOT_TAC THEN PEM_PATH_DISCHARGE_TAIL_TAC;;

(* ------------------------------------------------------------------------- *)
(* The whole function.                                                       *)
(* ------------------------------------------------------------------------- *)

let PEM_FULL_TAC p =
  PEM_INTRO_TAC p THEN PEM_SETUP_TAC p THEN
  PEM_DECLASS_TAC p THEN PEM_STATES_TAC THEN PEM_MINIMAL_TAC p THEN
  ENSURES_EVENTS_SEQUENCE_TAC (parse_term("pc + " ^ p.pfn ^ "_" ^ p.pexit)) (PEM_A2 p) THEN
  CONJ_TAC THENL
   [ENSURES_EVENTS_SEQUENCE_TAC (parse_term("pc + " ^ p.pfn ^ "_" ^ p.pa1)) (PEM_A1 p) THEN
    CONJ_TAC THENL
     [PEM_PART1_TAC p;
      ASM_CASES_TAC `k0 = 0` THENL [PEM_NOLOOP_TAC p; PEM_LOOP_TAC p]];
    PEM_PART3_TAC p];;

