(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the constant-time and memory safety proofs of the API functions *)
(* of mlkem_native2 (keypair_derand, enc_derand, dec and the internal        *)
(* pke_encrypt and pke_decrypt): the theorems of their callees in the forms  *)
(* the proofs need (the safety of the kernels with the frames of their       *)
(* correctness theorems; mlkem_check_encoding and mlkem_hash_g, on whose     *)
(* results the callers' events depend, as correctness and safety in one,     *)
(* "FULL"), the loops as single steps, and the proof of each function for a  *)
(* parameter set, given the theorems of the callees that depend on it.       *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native2_kem.ml";;
needs "arm/proofs/utils/mlkem_native2_safety.ml";;
needs "arm/proofs/utils/mlkem_native2_keccak_full.ml";;

(* ------------------------------------------------------------------------- *)
(* The safety of the kernels with the frames of their correctness theorems,  *)
(* as callers need them (their safety theorems have the frame \s s'. true):  *)
(* for those without a stack, from the correctness theorem by mk_safety_spec *)
(* ~keep_maychanges:true; for those that save D8-D15, that of the core and   *)
(* then of the subroutine with the saving. Those of the kernels that depend  *)
(* on the parameter set are made in the same ways by the proof of each       *)
(* parameter set, for its own.                                               *)
(* ------------------------------------------------------------------------- *)

let core_safe_of core_correct sub_safe =
  let cvs,cimp = strip_forall(concl core_correct) in
  let chyp,cens = dest_imp cimp in
  let _,cargs = strip_comb cens in
  let cpre = el 1 cargs and cpost = el 2 cargs and cframe = el 3 cargs in
  let s,cpre_b = dest_abs cpre in
  let keep c =
    let h = fst(strip_comb c) in
    (is_const h && (name_of h = "aligned_bytes_loaded" ||
                    name_of h = "C_ARGUMENTS")) ||
    (is_eq c && (try rator(lhand c) = `read PC` with Failure _ -> false)) in
  let fv,sbody = dest_exists(concl sub_safe) in
  let svs,simp = strip_forall sbody in
  let ev = hd svs in
  let _,sens = dest_imp simp in
  let _,sargs = strip_comb sens in
  let spost = el 2 sargs in
  let s2,spost_b = dest_abs spost in
  let exc = find is_exists (conjuncts spost_b) in
  let e2,exb = dest_exists exc in
  let c1,c23 = dest_conj exb in
  let c2,c3 = dest_conj c23 in
  let fh,fargs = strip_comb(rand c2) in
  let fargs' = butlast(butlast fargs) in
  let fv' = mk_var("f_events",
    itlist (fun a t -> mk_fun_ty (type_of a) t) fargs' `:(uarch_event)list`) in
  let c2' = mk_eq(e2,list_mk_comb(fv',fargs')) in
  let mh,margs = strip_comb c3 in
  let nost l =
    let ls = dest_list l in
    mk_list(filter (fun p -> not(free_in `stackpointer:int64` p)) ls,
            type_of(hd ls)) in
  let c3' = list_mk_comb(mh,[e2; nost(el 1 margs); nost(el 2 margs)]) in
  let s3,cpost_b = dest_abs cpost in
  let pcpost = hd(conjuncts cpost_b) in
  let ex' = mk_exists(e2,list_mk_conj[vsubst [s3,s2] c1; c2'; c3']) in
  let pre' = mk_abs(s,list_mk_conj(filter keep (conjuncts cpre_b) @
               [mk_eq(mk_comb(`read events`,s),ev)])) in
  let post' = mk_abs(s3,mk_conj(pcpost,ex')) in
  let ens' = list_mk_comb(fst(strip_comb cens),
                          [hd cargs; pre'; post'; cframe]) in
  let body = mk_imp(chyp,ens') in
  let vs' = ev :: filter (fun v -> free_in v body) cvs in
  mk_exists(fv',list_mk_forall(vs',body));;

let framed_of safe correct =
  let c = concl safe in
  let fv,body = dest_exists c in
  let vs,imp = strip_forall body in
  let hyp,ens = dest_imp imp in
  let cfr = rand(snd(dest_imp(snd(strip_forall(concl correct))))) in
  mk_exists(fv,list_mk_forall(vs,mk_imp(hyp,mk_comb(rator ens,cfr))));;

(* The framed safety of a kernel with the stack: the core by the simulation
 * of the code, then the subroutine with the saving of D8-D15, then with
 * the BTI landing pad
 *)

let FRAMED_STACK_KERNEL core_correct sub_safe sub_correct exec nsteps
                        mc tmc =
  let ctm = core_safe_of core_correct sub_safe in
  let pubs = fst(strip_forall(snd(dest_exists ctm))) in
  let cth = prove(ctm,
    PROVE_SAFETY_SPEC_TAC ~public_vars:pubs exec) in
  let sth = prove(framed_of sub_safe sub_correct,
    ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:nsteps exec cth
      `[D8; D9; D10; D11; D12; D13; D14; D15]` 64 THEN
    DISCHARGE_SAFETY_PROPERTY_TAC) in
  cth,sth,ARM_ADD_IBT_RULE mc tmc sth;;

let framed_kernel_safe name correct exec =
  let spec,pubs = mk_safety_spec ~keep_maychanges:true
                   (assoc name subroutine_signatures) correct exec in
  prove(spec,PROVE_SAFETY_SPEC_TAC ~public_vars:pubs exec);;

let MLKEM_FROMBYTES_NOIBT_SUBROUTINE_SAFE_FRAMED =
  framed_kernel_safe "mlkem_frombytes"
    MLKEM_FROMBYTES_NOIBT_SUBROUTINE_CORRECT
    MLKEM_FROMBYTES_EXEC;;

let MLKEM_FROMBYTES_SUBROUTINE_SAFE_FRAMED =
  ARM_ADD_IBT_RULE mlkem_frombytes_mc mlkem_frombytes_tmc
    MLKEM_FROMBYTES_NOIBT_SUBROUTINE_SAFE_FRAMED;;

let MLKEM_FROMMSG_NOIBT_SUBROUTINE_SAFE_FRAMED =
  framed_kernel_safe "mlkem_frommsg"
    MLKEM_FROMMSG_NOIBT_SUBROUTINE_CORRECT
    MLKEM_FROMMSG_EXEC;;

let MLKEM_FROMMSG_SUBROUTINE_SAFE_FRAMED =
  ARM_ADD_IBT_RULE mlkem_frommsg_mc mlkem_frommsg_tmc
    MLKEM_FROMMSG_NOIBT_SUBROUTINE_SAFE_FRAMED;;

let MLKEM_MULCACHE_COMPUTE_SUBROUTINE_SAFE_FRAMED =
  framed_kernel_safe "mlkem_mulcache_compute"
    MLKEM_MULCACHE_COMPUTE_SUBROUTINE_CORRECT
    MLKEM_MULCACHE_COMPUTE_EXEC;;

let MLKEM_TOMONT_SUBROUTINE_SAFE_FRAMED =
  framed_kernel_safe "mlkem_tomont"
    MLKEM_TOMONT_SUBROUTINE_CORRECT
    MLKEM_TOMONT_EXEC;;

let MLKEM_REDUCE_SUBROUTINE_SAFE_FRAMED =
  framed_kernel_safe "mlkem_reduce"
    MLKEM_REDUCE_SUBROUTINE_CORRECT
    MLKEM_REDUCE_EXEC;;

let MLKEM_ADD_REDUCE_NOIBT_SUBROUTINE_SAFE_FRAMED =
  framed_kernel_safe "mlkem_add_reduce"
    MLKEM_ADD_REDUCE_NOIBT_SUBROUTINE_CORRECT
    MLKEM_ADD_REDUCE_EXEC;;

let MLKEM_ADD_REDUCE_SUBROUTINE_SAFE_FRAMED =
  ARM_ADD_IBT_RULE mlkem_add_reduce_mc mlkem_add_reduce_tmc
    MLKEM_ADD_REDUCE_NOIBT_SUBROUTINE_SAFE_FRAMED;;

let MLKEM_SUB_REDUCE_NOIBT_SUBROUTINE_SAFE_FRAMED =
  framed_kernel_safe "mlkem_sub_reduce"
    MLKEM_SUB_REDUCE_NOIBT_SUBROUTINE_CORRECT
    MLKEM_SUB_REDUCE_EXEC;;

let MLKEM_SUB_REDUCE_SUBROUTINE_SAFE_FRAMED =
  ARM_ADD_IBT_RULE mlkem_sub_reduce_mc mlkem_sub_reduce_tmc
    MLKEM_SUB_REDUCE_NOIBT_SUBROUTINE_SAFE_FRAMED;;

let MLKEM_TOBYTES_ALT_NOIBT_SUBROUTINE_SAFE_FRAMED =
  framed_kernel_safe "mlkem_tobytes_alt"
    MLKEM_TOBYTES_ALT_NOIBT_SUBROUTINE_CORRECT
    MLKEM_TOBYTES_ALT_EXEC;;

let MLKEM_TOBYTES_ALT_SUBROUTINE_SAFE_FRAMED =
  ARM_ADD_IBT_RULE mlkem_tobytes_alt_mc mlkem_tobytes_alt_tmc
    MLKEM_TOBYTES_ALT_NOIBT_SUBROUTINE_SAFE_FRAMED;;

let MLKEM_TOMSG_NOIBT_SUBROUTINE_SAFE_FRAMED =
  framed_kernel_safe "mlkem_tomsg"
    MLKEM_TOMSG_NOIBT_SUBROUTINE_CORRECT
    MLKEM_TOMSG_EXEC;;

let MLKEM_TOMSG_SUBROUTINE_SAFE_FRAMED =
  ARM_ADD_IBT_RULE mlkem_tomsg_mc mlkem_tomsg_tmc
    MLKEM_TOMSG_NOIBT_SUBROUTINE_SAFE_FRAMED;;

let MLKEM_NTT_ALT_CORE_SAFE_FRAMED,
    MLKEM_NTT_ALT_NOIBT_SUBROUTINE_SAFE_FRAMED,
    MLKEM_NTT_ALT_SUBROUTINE_SAFE_FRAMED =
  FRAMED_STACK_KERNEL MLKEM_NTT_ALT_CORRECT
    MLKEM_NTT_ALT_NOIBT_SUBROUTINE_SAFE
    MLKEM_NTT_ALT_NOIBT_SUBROUTINE_CORRECT
    MLKEM_NTT_ALT_EXEC (5,5)
    mlkem_ntt_alt_mc mlkem_ntt_alt_tmc;;

let MLKEM_INTT_ALT_CORE_SAFE_FRAMED,
    MLKEM_INTT_ALT_NOIBT_SUBROUTINE_SAFE_FRAMED,
    MLKEM_INTT_ALT_SUBROUTINE_SAFE_FRAMED =
  FRAMED_STACK_KERNEL MLKEM_INTT_ALT_CORRECT
    MLKEM_INTT_ALT_NOIBT_SUBROUTINE_SAFE
    MLKEM_INTT_ALT_NOIBT_SUBROUTINE_CORRECT
    MLKEM_INTT_ALT_EXEC (5,5)
    mlkem_intt_alt_mc mlkem_intt_alt_tmc;;

(* ------------------------------------------------------------------------- *)
(* The modulus check mlkem_check_encoding as correctness and safety in one:  *)
(* the result of CORRECT and the events of SAFE (which do not depend on the  *)
(* data), with the frame of CORRECT, without and with the BTI landing pad.   *)
(* ------------------------------------------------------------------------- *)

let MLKEM_CHECK_ENCODING_NOIBT_SUBROUTINE_FULL = time prove
 (`exists f_events.
     forall e a k n pc returnaddress.
         val k < 2 EXP 61
         ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_check_encoding_tmc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; k] s /\
                  read (memory :> bytes(a,384 * val k)) s = n /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  C_RETURN s =
                  (if !i. i < 256 * val k
                          ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329
                   then word 1 else word 0) /\
                  (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events a k pc returnaddress /\
                      memaccess_inbounds e2 [a,(384 * val k) * 1] []))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (k:int64) (pc:num) (returnaddress:int64).
      if val k = 0 then f_ev_zero a k pc returnaddress
      else APPEND (f_ev_epil a k pc returnaddress)
                  (APPEND (ENUMERATEL (8 * val k)
                             (\i. f_ev_loop a k pc returnaddress i))
                          (f_ev_prol a k pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `a:int64` THEN W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; fst MLKEM_CHECK_ENCODING_EXEC] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; LT] THEN ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_CHECK_ENCODING_EXEC [n] THEN
                        SIMD_SIMPLIFY_TAC[]) (1--31) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `word_shl (word k:int64) 3 = word(8 * k)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SHL; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC MOD_DOWN_CONV THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 3 * k = 8 * k`];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word(8 * k):int64) = 8 * k /\ ~(8 * k = 0)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `k < 2 EXP 61` THEN ARITH_TAC;
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `8 * k` `pc + 0x4c` `pc + 0x98`
   `\i s. read X30 s = returnaddress /\
          read X0 s = word_add a (word(48 * i)) /\
          read X4 s = word(8 * k - i) /\
          read Q29 s = word 0xfff00ffffff00ffffff00ffffff00fff /\
          read Q31 s = word 0x0b0a0a09080707060504040302010100 /\
          read (memory :> bytes(a,384 * k)) s = n /\
          (!j. j < 32
               ==> (word_uge
                     (word_subword
                       (word_join
                         (word_join (read Q19 s) (read Q18 s):256 word)
                         (word_join (read Q17 s) (read Q16 s):256 word)
                        :512 word) (16 * j,16):int16)
                     (word(if EVEN j then 3329 else 53264)) <=>
                    ?t. t < i /\ cenc_bad n (32 * t + j)))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** The initialization, with all lanes 0 ***)

    ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_CHECK_ENCODING_EXEC [n] THEN
                        SIMD_SIMPLIFY_TAC[]) (1--19) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0; LT] THEN
    CONJ_TAC THENL
     [CONV_TAC WORD_REDUCE_CONV THEN
      REWRITE_TAC[word_subword; VAL_WORD_0; DIV_0; MOD_0; WORD_UGE] THEN
      GEN_TAC THEN COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV THEN
      ARITH_TAC;
      DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The loop body, on the 384-bit chunk c of the input ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `word_sub (word (8 * k - i)) (word 1):int64 = word(8 * k - (i + 1)) /\
      val(word(8 * k - (i + 1)):int64) = 8 * k - (i + 1)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(ISPECL [`8 * k - i`; `1`]
          (INST_TYPE [`:64`,`:N`] WORD_SUB)) THEN
        ASM_SIMP_TAC[ARITH_RULE `i < 8 * k ==> 1 <= 8 * k - i`] THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN ARITH_TAC;
        REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        UNDISCH_TAC `k < 2 EXP 61` THEN ARITH_TAC];
      ALL_TAC] THEN
    ABBREV_TAC
     `c:384 word = word((n DIV 2 EXP (8 * (48 * i))) MOD 2 EXP 384)` THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    MAP_EVERY ABBREV_TAC
     [`m0 = read Q16 s0`; `m1 = read Q17 s0`; `m2 = read Q18 s0`;
      `m3 = read Q19 s0`] THEN
    MP_TAC(SPECL [`a:int64`; `384 * k`; `n:num`; `48 * i`; `s0:armstate`]
      CHECK_ENCODING_LOADS) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [UNDISCH_TAC `i < 8 * k` THEN ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
    MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_CHECK_ENCODING_EXEC [n] THEN
                        SIMD_SIMPLIFY_TAC[]) (1--19) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      CONV_TAC WORD_RULE;
      FIRST_X_ASSUM(MP_TAC o check (can (term_match []
        `!j. j < 32 ==> (word_uge x y <=> ?t. t < i /\ P t j)`) o concl)) THEN
      ASM_REWRITE_TAC[] THEN
      CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV THENC
                         SIMD_SIMPLIFY_CONV[])) THEN
      STRIP_TAC THEN
      MP_TAC(SPECL [`n:num`; `i:num`; `c:384 word`] CHECK_ENCODING_FIELD) THEN
      ASM_REWRITE_TAC[] THEN
      CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
      STRIP_TAC THEN
      CONV_TAC(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV THENC
               SIMD_SIMPLIFY_CONV[]) THEN
      REWRITE_TAC[WORD_UGE_UMAX; EXISTS_LT_ADD1] THEN ASM_REWRITE_TAC[] THEN
      LANE_ARGS_BITBLAST_TAC 8 [];
      DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The combination of the maxima, the comparison and the return ***)

    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    MAP_EVERY ABBREV_TAC
     [`m0 = read Q16 s0`; `m1 = read Q17 s0`; `m2 = read Q18 s0`;
      `m3 = read Q19 s0`] THEN
    FIRST_X_ASSUM(MP_TAC o check (can (term_match []
      `!j. j < 32 ==> (word_uge x y <=> ?t. t < i /\ P t j)`) o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV THENC
                       SIMD_SIMPLIFY_CONV[])) THEN
    STRIP_TAC THEN
    MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_CHECK_ENCODING_EXEC [n] THEN
                        SIMD_SIMPLIFY_TAC[]) (1--12) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[WORD_UGE_UMAX] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[CHECK_ENCODING_MASK_MAX; CHECK_ENCODING_ALL] THEN
      CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC
                         NUM_REDUCE_CONV)) THEN
      W(fun (asl,w) ->
        let bv = find_term (fun t -> match t with
                     Comb(Const("bitval",_),_) -> true | _ -> false) w in
        let d = rand bv in
        SUBGOAL_THEN (mk_eq(lhand w,mk_cond(d,`word 0:int64`,`word 1:int64`)))
        SUBST1_TAC THENL
         [SPEC_TAC(d,`b:bool`) THEN GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
          REWRITE_TAC[BITVAL_CLAUSES] THEN
          CONV_TAC(WORD_REDUCE_CONV THENC NUM_REDUCE_CONV) THEN REWRITE_TAC[];
          GEN_REWRITE_TAC LAND_CONV [GSYM COND_SWAP] THEN
          AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
          REWRITE_TAC[DE_MORGAN_THM] THEN
          W(fun (_,w) -> ACCEPT_TAC(CONJ_ACI_RULE w))]);
      DISCHARGE_SAFETY_PROPERTY_TAC]]);;

let MLKEM_CHECK_ENCODING_SUBROUTINE_FULL =
  ARM_ADD_IBT_RULE mlkem_check_encoding_mc mlkem_check_encoding_tmc
    MLKEM_CHECK_ENCODING_NOIBT_SUBROUTINE_FULL;;

(* ------------------------------------------------------------------------- *)
(* The hash G (mlkem_hash_g) as correctness and safety in one for messages   *)
(* of one block (less than 72 bytes, e.g. the 33 bytes d || k of key         *)
(* generation): the whole words and the single bytes of the block, the       *)
(* padding and the permutation in FULL form, as the lemmas of its            *)
(* correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

(*** The decrement of a loop counter and the test after it, with the
 *** bounds from the assumptions
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
   [`inp:int64,LENGTH(m:byte list)`;
    `word_add stackpointer (word 48):int64,200`]
   [`word_add stackpointer (word 48):int64,200`],
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
  ASM_CASES_TAC `t DIV 8 = 0` THEN ASM_REWRITE_TAC[] THENL
   [ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC MLKEM_HASH_G_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; EXP; MOD_1; WORD_XOR_0;
                    WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `t DIV 8` `pc + mlkem_hash_g_lastwords`
   `pc + mlkem_hash_g_lastbytes`
   `\k s. read SP s = stackpointer /\
          read X0 s = word_add stackpointer (word(48 + 8 * k)) /\
          read X1 s = word(t DIV 8 - k) /\
          read X20 s = word_add inp (word(72 * q + 8 * k)) /\
          read X21 s = word t /\
          read X22 s = c /\
          read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
          read (memory :> bytes(c,192)) s =
          num_of_wordlist round_constants /\
          read (memory :> wbytes(word_add stackpointer (word 48))) s =
          word_xor (A:1600 word)
           (word((num_of_bytelist m DIV 2 EXP (8 * 72 * q)) MOD
                 2 EXP (64 * k)))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** The entry, past the test for no whole words ***)

    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC MLKEM_HASH_G_EXEC (1--5) THEN
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
                  `72 * q + 8 * k`; `s0:armstate`]
      READ_MEMORY_BYTES64_OF_NUM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ARM_STEPS_TAC MLKEM_HASH_G_EXEC (1--6) THEN
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
   [`inp:int64,LENGTH(m:byte list)`;
    `word_add stackpointer (word 48):int64,200`]
   [`word_add stackpointer (word 48):int64,200`],
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
  SUBGOAL_THEN `word_and (word t:int64) (word 7) = word(t MOD 8)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`word t:int64`; `3`] (CONJUNCT1 WORD_AND_MASK_WORD)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t MOD 8 < 8` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `t MOD 8` THEN
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
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC MLKEM_HASH_G_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ARITH_RULE `64 * t DIV 8 = 8 * (8 * t DIV 8)`] THEN
    REPEAT CONJ_TAC THEN TRY(ASM_SIMP_TAC[MOD_LT] THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `t MOD 8` `pc + mlkem_hash_g_lastbyte`
   `pc + mlkem_hash_g_pad`
   `\k s. read SP s = stackpointer /\
          read X0 s = word_add stackpointer (word(48 + 8 * t DIV 8 + k)) /\
          read X1 s = word(t MOD 8 - k) /\
          read X20 s = word_add inp (word(72 * q + 8 * t DIV 8 + k)) /\
          read X21 s = word t /\
          read X22 s = c /\
          read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
          read (memory :> bytes(c,192)) s =
          num_of_wordlist round_constants /\
          read (memory :> wbytes(word_add stackpointer (word 48))) s =
          word_xor (A:1600 word)
           (word((num_of_bytelist m DIV 2 EXP (8 * 72 * q)) MOD
                 2 EXP (8 * (8 * t DIV 8 + k))))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** The entry, past the test for no single bytes ***)

    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC MLKEM_HASH_G_EXEC (1--2) THEN
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
                  `72 * q + 8 * t DIV 8 + k`; `s0:armstate`]
      READ_MEMORY_BYTES8_OF_NUM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ARM_STEPS_TAC MLKEM_HASH_G_EXEC (1--6) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BYTE_XOR_ZX]) THEN
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
   [`word_add stackpointer (word 48):int64,200`; `c:int64,192`;
    `word_sub stackpointer (word 128):int64,128`]
   [`word_add stackpointer (word 48):int64,200`;
    `word_sub stackpointer (word 128):int64,128`],
  ASSUME_CALLEE_TAILED_TAC SHA3_KECCAK_F1600_SUBROUTINE_FULL_F1600 "H_K1" THEN
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
  ARM_STEPS_TAC MLKEM_HASH_G_EXEC (1--3) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[BYTE_XOR_CONST_ZX]) THEN
  SUBGOAL_THEN
   `!j. j < 200
        ==> read (memory :> bytes8
                   (word_add stackpointer (word (48 + j)))) s3 =
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
  ARM_STEPS_TAC MLKEM_HASH_G_EXEC (4--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[BYTE_XOR_CONST_ZX]) THEN
  SUBGOAL_THEN
   `read (memory :> wbytes (word_add stackpointer (word 48))) s9 =
    word_xor (word_xor (A:1600 word) (word(2 EXP (8 * t) * 6)))
             (word(2 EXP (8 * 71) * 128))`
  ASSUME_TAC THENL
   [REWRITE_TAC[READ_MEMORY_WBYTES_BYTES] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    ASM_SIMP_TAC[BYTE_XOR_SHIFT; ARITH_RULE `128 < 256 /\ 71 < 200`] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN

  (*** The permutation ***)

  SUBGOAL_THEN `wordlist_from_memory(c,24) s9 = round_constants`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[WORDLIST_FROM_MEMORY_ROUND_CONSTANTS]; ALL_TAC] THEN
  REMOVE_THEN "H_K1" (fun th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
     (mlkem_native2_image_mc,MLKEM_HASH_G_EXEC,layout "sha3_keccak_f1600",
      sha3_keccak_f1600_mc,th)
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`;
      `word_xor (word_xor (A:1600 word) (word(2 EXP (8 * t) * 6)))
                (word(2 EXP (8 * 71) * 128))`;
      `pc + sha3_keccak_f1600`; `read SP s`; `read X30 s`] 10 THENL
     [EXISTS_E2_TAC (ref [`t:num`; `c:int64`; `stackpointer:int64`;
                          `pc:num`]);
      LABEL_TAC "H_K1" th]) THEN
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
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
     (mlkem_native2_image_mc,MLKEM_HASH_G_EXEC,0,mlkem_native2_image_mc,
      FRESH_TAIL_RULE th') [] n THENL
     [EXISTS_E2_TAC (ref hg_vars); LABEL_TAC label th]);;

let MLKEM_HASH_G_SHORT_SUBROUTINE_FULL = time prove
 (`exists f_events.
     forall e out inp (m:byte list) len c pc stackpointer returnaddress.
       aligned 16 stackpointer /\ LENGTH m = len /\ len < 72 /\
       ALL (nonoverlapping (word_sub stackpointer (word 384),384))
           [(word pc,mlkem_native2_image_size); (out,64); (inp,len);
            (c,192)] /\
       nonoverlapping (out,64) (word pc,mlkem_native2_image_size)
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read PC s = word(pc + mlkem_hash_g) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [out; inp; word len; c] s /\
                 read (memory :> bytes(inp,len)) s = num_of_bytelist m /\
                 wordlist_from_memory(c,24) s = round_constants /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 read (memory :> bytes(out,64)) s =
                 num_of_bytelist(sha3_512 m) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events inp len c out pc
                           (word_sub stackpointer (word 384)) returnaddress /\
                    memaccess_inbounds e2
                     [inp,len; c,192; out,64;
                      word_sub stackpointer (word 384),384]
                     [out,64; word_sub stackpointer (word 384),384]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(out,64);
               memory :> bytes(word_sub stackpointer (word 384),384)])`,
  ASSUME_CALLEE_TAILED_TAC MLKEM_HASH_G_WORDS_FULL "H_W" THEN
  ASSUME_CALLEE_TAILED_TAC MLKEM_HASH_G_BYTES_FULL "H_B" THEN
  ASSUME_CALLEE_TAILED_TAC MLKEM_HASH_G_PAD_FULL "H_P" THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `out:int64`; `inp:int64`; `m:byte list`;
    `len:num`; `c:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 384 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `len < 2 EXP 64` ASSUME_TAC THENL
   [UNDISCH_TAC `len < 72` THEN ARITH_TAC; ALL_TAC] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29` THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORDLIST_FROM_MEMORY_ROUND_CONSTANTS]) THEN
  ARM_STEPS_TAC MLKEM_HASH_G_EXEC (1--18) THEN
  SUBGOAL_THEN
   `read (memory :> wbytes (word_add stackpointer (word 176))) s18 =
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
    `word_add stackpointer (word 128):int64`; `0`; `len:num`;
    `word 0:1600 word`] 19 THEN
  HG_LEMMA_CALL_TAC "H_B"
   [`m:byte list`; `inp:int64`; `c:int64`; `pc:num`;
    `word_add stackpointer (word 128):int64`; `0`; `len:num`;
    `word 0:1600 word`] 20 THEN
  HG_LEMMA_CALL_TAC "H_P"
   [`inp:int64`; `len:num`; `c:int64`; `pc:num`;
    `word_add stackpointer (word 128):int64`; `len:num`;
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
    MP_TAC(SPECL [`word_add stackpointer (word 176):int64`; `200`;
                  `val(S:1600 word)`; k; `s21:armstate`]
      READ_MEMORY_BYTES128_OF_NUM))
   [`0`; `16`; `32`; `48`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  REWRITE_TAC[WORD_ADD_0; DIV_1] THEN REPEAT DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_HASH_G_EXEC (22--39) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
    MP_TAC(SPECL [`out:int64`; `4`; `val(S:1600 word)`; `s39:armstate`]
      READ_MEMORY_BYTES_OF_BYTES128) THEN
    CONV_TAC(LAND_CONV(LAND_CONV EXPAND_CASES_CONV)) THEN
    CONV_TAC(LAND_CONV(LAND_CONV NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[ARITH_RULE `16 * 4 = 64 /\ 128 * 4 = 512`] THEN
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
(* The zeroing of a stack buffer as one step, with its events.               *)
(* ------------------------------------------------------------------------- *)

(*** The zeroing of len bytes at stackpointer + off with stp q0, q0 and a
 *** count in X1, from start (setup instructions before the loop) to stop
 ***)

let api_zero_safe_tm start stop off len =
  let ns = mk_small_numeral in
  vsubst [ns start,`start:num`; ns stop,`stop:num`; ns off,`off:num`;
          ns len,`len:num`]
  `exists f_events.
     forall e stackpointer pc.
       nonoverlapping (word_add stackpointer (word off),len)
                      (word pc,mlkem_native2_image_size)
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read PC s = word(pc + start) /\
                 read SP s = stackpointer /\
                 read events s = e)
            (\s. read PC s = word(pc + stop) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events stackpointer pc /\
                    memaccess_inbounds e2
                     [word_add stackpointer (word off),len]
                     [word_add stackpointer (word off),len]))
            (MAYCHANGE [PC; X0; X1] ,, MAYCHANGE [Q0] ,,
             MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
             MAYCHANGE [memory :> bytes(word_add stackpointer (word off),
                                        len)])`;;

let API_ZERO_SAFE_TAC exec start setup stop off len =
  let n = len / 32 and ns = mk_small_numeral in
  let inv = vsubst [ns off,`off:num`; ns len,`len:num`]
   `\i s. read X0 s = word_add stackpointer (word(off + 32 * i)) /\
          read X1 s = word(len - 32 * i)` in
  let pcp k = mk_binop `(+):num->num->num` `pc:num` (ns k) in
  let ilt = vsubst [ns n,`n:num`] `i < n` in
  CONCRETIZE_F_EVENTS_TAC
   (vsubst [ns n,`n:num`]
     `\(stackpointer:int64) (pc:num).
        APPEND (f_ev_epil stackpointer pc)
               (APPEND (ENUMERATEL n (\i. f_ev_loop stackpointer pc i))
                       (f_ev_prol stackpointer pc)) :(uarch_event)list`) THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `pc:num`] THEN
  DISCH_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC (ns n) (pcp (start + 4 * setup)) (pcp stop)
   inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false exec (1--setup) THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN (vsubst [ns len,`len:num`]
     `word_sub (word(len - 32 * i)) (word 32):int64 =
      word(len - 32 * (i + 1)) /\
      val(word(len - 32 * (i + 1)):int64) = len - 32 * (i + 1)`)
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(ISPECL [mk_binop `(-):num->num->num` (ns len)
                         `32 * i`; `32`]
          (INST_TYPE [`:64`,`:N`] WORD_SUB)) THEN
        ASM_SIMP_TAC[ARITH_RULE(mk_imp(ilt,
          vsubst [ns len,`len:num`] `32 <= len - 32 * i`))] THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
        REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        ASM_ARITH_TAC];
      ALL_TAC] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false exec (1--3) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE(vsubst [ns len,`len:num`; ns n,`n:num`]
        `32 * (i + 1) < len <=> i + 1 < n`)] THEN
      COND_CASES_TAC THEN REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false exec [] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

(* ------------------------------------------------------------------------- *)
(* The calls of the kernels by their safety theorems, and the proofs of      *)
(* pke_encrypt and pke_decrypt for k.                                        *)
(* ------------------------------------------------------------------------- *)

(*** The instantiation of a framed safety theorem th of the callee name:
 *** e, the C arguments from the registers, the PC, the stack pointer and
 *** the return address
 ***)

let safe_ilist th name =
  let vs = fst(strip_forall(snd(dest_exists(concl th)))) in
  let ca = find_term (fun t ->
    is_comb t && is_comb(rator t) &&
    (try fst(dest_const(rator(rator t))) = "C_ARGUMENTS"
     with Failure _ -> false)) (concl th) in
  let args = dest_list(rand(rator ca)) in
  map (fun v ->
    let n = name_of v in
    if n = "e" then v
    else if n = "pc" then parse_term("pc + "^name)
    else if n = "stackpointer" then `read SP s`
    else if n = "returnaddress" then `read X30 s`
    else
      let i = index v args in
      parse_term("read X"^string_of_int i^" s")) vs;;

(*** The framed safety theorems of the kernels, with their labels, to which
 *** the proof of a parameter set adds those of its own kernels
 ***)

let api_safe_kernels = ref
  ["mlkem_frombytes","H_FROMBYTES",MLKEM_FROMBYTES_SUBROUTINE_SAFE_FRAMED,
   mlkem_frombytes_mc;
   "mlkem_frommsg","H_FROMMSG",MLKEM_FROMMSG_SUBROUTINE_SAFE_FRAMED,
   mlkem_frommsg_mc;
   "mlkem_ntt_alt","H_NTT",MLKEM_NTT_ALT_SUBROUTINE_SAFE_FRAMED,
   mlkem_ntt_alt_mc;
   "mlkem_intt_alt","H_INTT",MLKEM_INTT_ALT_SUBROUTINE_SAFE_FRAMED,
   mlkem_intt_alt_mc;
   "mlkem_mulcache_compute","H_MULCACHE",
   MLKEM_MULCACHE_COMPUTE_SUBROUTINE_SAFE_FRAMED,mlkem_mulcache_compute_mc;
   "mlkem_tomont","H_TOMONT",MLKEM_TOMONT_SUBROUTINE_SAFE_FRAMED,
   mlkem_tomont_mc;
   "mlkem_reduce","H_REDUCE",MLKEM_REDUCE_SUBROUTINE_SAFE_FRAMED,
   mlkem_reduce_mc;
   "mlkem_add_reduce","H_ADD",MLKEM_ADD_REDUCE_SUBROUTINE_SAFE_FRAMED,
   mlkem_add_reduce_mc;
   "mlkem_sub_reduce","H_SUB",MLKEM_SUB_REDUCE_SUBROUTINE_SAFE_FRAMED,
   mlkem_sub_reduce_mc;
   "mlkem_tobytes_alt","H_TOBYTES",MLKEM_TOBYTES_ALT_SUBROUTINE_SAFE_FRAMED,
   mlkem_tobytes_alt_mc;
   "mlkem_tomsg","H_TOMSG",MLKEM_TOMSG_SUBROUTINE_SAFE_FRAMED,
   mlkem_tomsg_mc];;

let api_add_safe_kernels l = api_safe_kernels := !api_safe_kernels @ l;;

(*** The assumptions of the safety of the kernels names and of the lemmas
 *** lems (label, theorem), and the calls of them for the run driver, with
 *** the public variables vars
 ***)

let API_SAFE_ASSUME_TAC names lems =
  let ks = filter (fun (n,_,_,_) -> mem n names) !api_safe_kernels in
  MAP_EVERY (fun (_,label,th,_) -> ASSUME_CALLEE_TAILED_TAC th label)
    ks THEN
  MAP_EVERY (fun (label,th) -> ASSUME_CALLEE_TAILED_TAC th label) lems;;

let api_safe_calls exec vars names lems =
  let ks = filter (fun (n,_,_,_) -> mem n names) !api_safe_kernels in
  map (fun (name,label,th,mc) ->
         layout name,
         NATIVE2_SAFE_THM_TAC exec vars label (layout name,mc) I
           (safe_ilist th name)) ks @
  map (fun (off,label,ilist) ->
         off,
         NATIVE2_SAFE_THM_TAC exec vars label (0,mlkem_native2_image_mc) I
           ilist) lems;;

let MLKEM_NATIVE2_PKE_ENCRYPT_SAFE_TAC k ex =
  let nm = api_param k in
  let names = ["mlkem_frombytes"; "mlkem_frommsg"; "mlkem_ntt_alt";
               "mlkem_mulcache_compute";
               "mlkem_basemul_k"^string_of_int k^"_alt"; "mlkem_intt_alt";
               "mlkem_add_reduce";
               "mlkem_compress_d"^string_of_int(api_du k);
               "mlkem_compress_d"^string_of_int(api_dv k)] in
  let z1s = pe_zero1 k in
  let z2s = z1s + 24 in
  let zl1 = 256 * k and uo = 96 + 768 * k and ul = 512 * k + 1024 in
  let z1 = prove(api_zero_safe_tm z1s z2s 96 zl1,
                 API_ZERO_SAFE_TAC ex z1s 3 z2s 96 zl1)
  and z2 = prove(api_zero_safe_tm z2s (z2s + 24) uo ul,
                 API_ZERO_SAFE_TAC ex z2s 3 (z2s + 24) uo ul) in
  let vars = [`ct:int64`; `at:int64`; `pk:int64`; `mp:int64`;
              `noise:int64`; `pc:num`; `stackpointer:int64`;
              `returnaddress:int64`] in
  let zil = [`e:(uarch_event)list`; `read SP s`; `pc:num`] in
  let calls = api_safe_calls ex vars names
                [z1s,"H_Z1",zil; z2s,"H_Z2",zil] in
  let ninit = if 1120 + 1280 * k < 4096 then 15 else 16 in
  let derive = [layout(nm ^ "_pke_encrypt") + 4 * ninit,
                (fun _ -> MLKEM_NATIVE_ADRP_TAC)] in
  API_SAFE_ASSUME_TAC names ["H_Z1",z1; "H_Z2",z2] THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
              (mk_const("X"^string_of_int n,[]))) (19--29) THEN
  ENSURES_INIT_TAC "s0" THEN
  NATIVE2_SAFE_RUN_TAC ex derive calls 0 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MEMACCESS_NUMERALS_TAC THEN NATIVE2_DISCHARGE_FRESH_TAC;;

let MLKEM_NATIVE2_PKE_DECRYPT_SAFE_TAC k ex =
  let nm = api_param k in
  let names = ["mlkem_decompress_d"^string_of_int(api_du k);
               "mlkem_decompress_d"^string_of_int(api_dv k);
               "mlkem_frombytes"; "mlkem_ntt_alt"; "mlkem_mulcache_compute";
               "mlkem_basemul_k"^string_of_int k^"_alt"; "mlkem_intt_alt";
               "mlkem_sub_reduce"; "mlkem_tomsg"] in
  let zs = pd_zero k and zl = 1280 * k + 1024 in
  let z = prove(api_zero_safe_tm zs (zs + 24) 96 zl,
                API_ZERO_SAFE_TAC ex zs 3 (zs + 24) 96 zl) in
  let vars = [`mp:int64`; `ct:int64`; `sk:int64`; `pc:num`;
              `stackpointer:int64`; `returnaddress:int64`] in
  let zil = [`e:(uarch_event)list`; `read SP s`; `pc:num`] in
  let calls = api_safe_calls ex vars names [zs,"H_Z",zil] in
  let ninit = if 1120 + 1280 * k < 4096 then 13 else 14 in
  let derive = [layout(nm ^ "_pke_decrypt") + 4 * ninit,
                (fun _ -> MLKEM_NATIVE_ADRP_TAC)] in
  API_SAFE_ASSUME_TAC names ["H_Z",z] THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
              (mk_const("X"^string_of_int n,[]))) (19--29) THEN
  ENSURES_INIT_TAC "s0" THEN
  NATIVE2_SAFE_RUN_TAC ex derive calls 0 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MEMACCESS_NUMERALS_TAC THEN NATIVE2_DISCHARGE_FRESH_TAC;;

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

(*** A call of a function of the image by its theorem with the label, all
 *** the variables but e_tail given (args), the lengths of slices and of the
 *** outputs of G rewritten
 ***)

let API_SAFE_SIM_TAC exec vars label args k =
  NATIVE2_SAFE_IMAGE_TAC exec vars [LENGTH_MLKEM_G; LENGTH_MLKEM_SLICE]
    label args k;;

(*** G = SHA3-512 on d || k by the FULL theorem, then rho and sigma, the
 *** constants for gen_matrix and rho as two 16-byte words
 ***)

let KP_HG_SAFE_CALL_TAC exec vars k kk gl =
  let d = `d:byte list` in
  let a = find_read_fact `X1` kk gl and sv = state_of kk in
  let m = mk_comb(mk_comb(`APPEND:byte list->byte list->byte list`,d),
                  mk_list([mk_comb(`word:num->byte`,mk_small_numeral k)],
                          `:byte`)) in
  let gin = SPECL [a; d; mk_comb(`word:num->byte`,mk_small_numeral k); sv]
              READ_MEMORY_BYTES_33_OF_PIECES in
  let ldth = find_asm (fun c ->
    c = mk_eq(mk_comb(`LENGTH:byte list->num`,d),`32`)) gl in
  let lenth = (REWRITE_CONV[LENGTH_APPEND; LENGTH; ldth] THENC
               NUM_REDUCE_CONV) (mk_comb(`LENGTH:byte list->num`,m)) in
  let r c = find_read_fact c kk gl in
  (MP_TAC gin THEN ANTS_TAC THENL
    [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
     CONV_TAC(DEPTH_CONV NUM_EXP_CONV) THEN ASM_REWRITE_TAC[] THEN NO_TAC;
     DISCH_TAC] THEN
   ASSUME_TAC lenth THEN
   FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[WORD_ADD] o
     MATCH_MP MLKEM_NATIVE2_ROUND_CONSTANTS o
     check (can (term_match [] `aligned_bytes_loaded s (word pc) mc`) o
            concl)) THEN
   API_SAFE_SIM_TAC exec vars "H_HG"
    [r `X0`; a; m; `33`; r `X3`; `pc:num`; r `SP`; r `X30`] kk THEN
   API_G_SPLIT_TAC (kk+1) THEN API_CONSTS_TAC THEN
   ASSUME_TAC(CONJUNCT1(ISPEC m LENGTH_MLKEM_G)) THEN
   KP_RHO_ABBREV_TAC THEN
   API_BYTES128_OF_32_AT_TAC (kp_spn(kp_cstack k + 160))
     `num_of_bytelist(rho:byte list)` (kk+1)) gl;;

(*** gen_matrix by its safety theorem: k = 2 without noise, else with the
 *** noise of s and e
 ***)

let KP_GM_SAFE_CALL_TAC exec vars k kk gl =
  let r c = find_read_fact c kk gl in
  let args =
    if k = 2 then
      [r `X0`; r `X1`; `rho:byte list`; r `X4`; r `X5`; r `X6`; `pc:num`;
       r `SP`; r `X30`]
    else
      [r `X0`; r `X1`; `rho:byte list`; r `X5`; kp_spn(kp_cstack k + 192);
       kp_spn(kp_s k); r `X4`; r `X6`; `pc:num`; r `SP`; r `X30`] in
  API_SAFE_SIM_TAC exec vars "H_GM" args kk gl;;

(*** mlkem_getnoise and mlkem_hash_h by their safety theorems ***)

let API_GETNOISE_SAFE_CALL_TAC exec vars kk gl =
  let v reg = mk_small_numeral(dest_small_numeral
                (rand(find_read_fact reg kk gl))) in
  let vs = vars @ fev_vars gl in
  REMOVE_THEN "H_GETNOISE" (fun th ->
    let th1 = SPECL [`e:(uarch_event)list`; find_read_fact `X0` kk gl;
                     find_read_fact `X1` kk gl; v `X2`; v `X3`; v `X4`;
                     v `X5`; find_read_fact `X6` kk gl; `pc:num`;
                     find_read_fact `SP` kk gl; find_read_fact `X30` kk gl]
                    th in
    let th2 = CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
               (REWRITE_RULE[ARITH_EQ] th1) in
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
     (mlkem_native2_image_mc,exec,0,mlkem_native2_image_mc,
      FRESH_TAIL_RULE th2) [] (kk+1)
    THENL [EXISTS_E2_TAC (ref vs); LABEL_TAC "H_GETNOISE" th]) gl;;

let API_HASH_H_SAFE_CALL_TAC exec vars kk gl =
  let r c = find_read_fact c kk gl in
  let len = mk_small_numeral(dest_small_numeral(rand(r `X2`))) in
  API_SAFE_SIM_TAC exec vars "H_HH"
   [r `X0`; r `X1`; len; r `X3`; `pc:num`; r `SP`; r `X30`] kk gl;;

(*** The proof of the safety of keypair_derand for k: the setup, the run
 *** and the end, as parts for debugging
 ***)

let kp_safe_parts k ex gmth =
  let nm = api_param k in
  let names = ["mlkem_ntt_alt"; "mlkem_mulcache_compute";
               "mlkem_basemul_k"^string_of_int k^"_alt"; "mlkem_tomont";
               "mlkem_add_reduce"; "mlkem_reduce"; "mlkem_tobytes_alt"] in
  let so = 256 + 512 * k * k and sl = 1280 * k in
  let z1 = prove(api_zero_safe_tm (kp_zero1 k) (kp_zero2 k) 96 160,
                 API_ZERO_SAFE_TAC ex (kp_zero1 k) 3 (kp_zero2 k) 96 160)
  and z2 = prove(api_zero_safe_tm (kp_zero2 k) (kp_zero2_stop k) so sl,
                 API_ZERO_SAFE_TAC ex (kp_zero2 k) (kp_zero2_setup k)
                   (kp_zero2_stop k) so sl) in
  let vars = [`pk:int64`; `sk:int64`; `coins:int64`; `pc:num`;
              `stackpointer:int64`; `returnaddress:int64`; `rho:byte list`] in
  let zil = [`e:(uarch_event)list`; `read SP s`; `pc:num`] in
  let calls =
    api_safe_calls ex vars names [kp_zero1 k,"H_Z1",zil; kp_zero2 k,"H_Z2",zil]
    @ [layout "mlkem_hash_g", KP_HG_SAFE_CALL_TAC ex vars k;
       layout "mlkem_gen_matrix", KP_GM_SAFE_CALL_TAC ex vars k;
       layout "mlkem_getnoise", API_GETNOISE_SAFE_CALL_TAC ex vars;
       layout "mlkem_hash_h", API_HASH_H_SAFE_CALL_TAC ex vars] in
  let derive = [layout(nm ^ "_keypair_derand") + 4 * 14,
                (fun _ -> MLKEM_NATIVE_ADRP_TAC)] in
  let setup =
    API_SAFE_ASSUME_TAC names ["H_Z1",z1; "H_Z2",z2] THEN
    ASSUME_CALLEE_TAILED_TAC MLKEM_HASH_G_SHORT_SUBROUTINE_FULL "H_HG" THEN
    ASSUME_CALLEE_TAILED_TAC gmth "H_GM" THEN
    ASSUME_CALLEE_TAILED_TAC MLKEM_GETNOISE_SUBROUTINE_SAFE "H_GETNOISE" THEN
    ASSUME_CALLEE_TAILED_TAC MLKEM_HASH_H_SUBROUTINE_SAFE "H_HH" THEN
    META_EXISTS_TAC THEN
    MAP_EVERY X_GEN_TAC
     [`e:(uarch_event)list`; `pk:int64`; `sk:int64`; `coins:int64`;
      `d:byte list`; `pc:num`] THEN
    WORD_FORALL_OFFSET_TAC (kp_stack k) THEN
    MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
                C_RETURN; ALL; PAIRWISE; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
    REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
    ABBREV_TAC(mk_eq(`rho:byte list`,kp_rho k)) THEN KP_RHO_ABBREV_TAC THEN
    ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
    ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
    MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
                (mk_const("X"^string_of_int n,[]))) (19--29) THEN
    ENSURES_INIT_TAC "s0" THEN
    API_BYTES128_OF_32_TAC `coins:int64` `num_of_bytelist(d:byte list)`
  and finish =
    ON_STATE(API_JOIN32_TAC
      (mk_comb(mk_comb(`word_add:int64->int64->int64`,`pk:int64`),
               mk_comb(`word:num->int64`,mk_small_numeral(384 * k))))
      `rho:byte list`) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MEMACCESS_NUMERALS_TAC THEN NATIVE2_DISCHARGE_FRESH_TAC in
  setup,derive,calls,finish;;

let MLKEM_NATIVE2_KEYPAIR_DERAND_SAFE_TAC k ex gmth =
  let setup,derive,calls,finish = kp_safe_parts k ex gmth in
  MLKEM_SAMPLENTT_TERMINATES_TAC (api_terminates_tm k (kp_rho k) true)
   (setup THEN NATIVE2_SAFE_RUN_TAC ex derive calls 0 THEN finish);;

(* ------------------------------------------------------------------------- *)
(* enc_derand: the modulus check by its FULL theorem and the case split on   *)
(* it; then H(pk), the matrix, G, the noise and K-PKE.Encrypt.               *)
(* ------------------------------------------------------------------------- *)

(*** The modulus check of ek at X0 by the FULL theorem, the result as
 *** mlkem_ek_check
 ***)

let API_CHECK_ENCODING_FULL_CALL_TAC exec vars k ek kk gl =
  let a = find_read_fact `X0` kk gl in
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
                      find_read_fact `X30` kk gl] th in
     let th2 = REWRITE_RULE[ARITH_RULE `2 < 2 EXP 61 /\ 3 < 2 EXP 61 /\
                                        4 < 2 EXP 61`;
                            ARITH_RULE `4096 = 2 EXP 12`]
                (CONV_RULE(ONCE_DEPTH_CONV WORD_NUM_RED_CONV THENC
                           ONCE_DEPTH_CONV NUM_MULT_CONV) th1) in
     ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native2_image_mc,exec,layout "mlkem_check_encoding",
       mlkem_check_encoding_mc,FRESH_TAIL_RULE th2) [] (kk+1)
     THENL [EXISTS_E2_TAC (ref vs); LABEL_TAC "H_CE" th]) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP eks lenth])) gl;;

(*** gen_matrix by its safety theorem, with rho from ek ***)

let EN_GM_SAFE_CALL_TAC exec vars k kk gl =
  let r c = find_read_fact c kk gl in
  let rho = en_rho k in
  let args =
    if k = 2 then
      [r `X0`; r `X1`; rho; r `X4`; r `X5`; r `X6`; `pc:num`; r `SP`;
       r `X30`]
    else
      [r `X0`; r `X1`; rho; r `X4`; `word 0:int64`; `word 0:int64`;
       `word 0:int64`; `pk:int64`; kp_spn(en_gin k + 32); r `X5`; r `X6`;
       `pc:num`; r `SP`; r `X30`] in
  (API_SLICE_AT_TAC `pk:int64` `ek:byte list` (384 * k) 32 kk THEN
   API_CONSTS_TAC THEN
   API_SAFE_SIM_TAC exec vars "H_GM" args kk) gl;;

(*** hash_g of 64 bytes by its safety theorem, and pke_encrypt ***)

let API_HASH_G_SAFE_CALL_TAC exec vars kk gl =
  let r c = find_read_fact c kk gl in
  let len = mk_small_numeral(dest_small_numeral(rand(r `X2`))) in
  API_SAFE_SIM_TAC exec vars "H_HGS"
   [r `X0`; r `X1`; len; r `X3`; `pc:num`; r `SP`; r `X30`] kk gl;;

let API_PKE_SAFE_CALL_TAC exec vars label regs kk gl =
  let r c = find_read_fact c kk gl in
  API_SAFE_SIM_TAC exec vars label
   (map r regs @ [`pc:num`; r `SP`; r `X30`]) kk gl;;

(*** The proof of the safety of enc_derand for k, with the safety theorem
 *** peth of pke_encrypt, as parts for debugging
 ***)

let en_safe_parts k ex gmth peth =
  let nm = api_param k in
  let zl = en_at k - en_gin k in
  let zth = prove(api_zero_safe_tm (en_zero k) (en_zero k + 24) 96 zl,
                  API_ZERO_SAFE_TAC ex (en_zero k) 3 (en_zero k + 24) 96 zl) in
  let vars = [`ct:int64`; `ss:int64`; `pk:int64`; `coins:int64`; `pc:num`;
              `stackpointer:int64`; `returnaddress:int64`; `ek:byte list`] in
  let zil = [`e:(uarch_event)list`; `read SP s`; `pc:num`] in
  let calls =
    api_safe_calls ex vars [] [en_zero k,"H_Z",zil] @
    [layout "mlkem_check_encoding",
       API_CHECK_ENCODING_FULL_CALL_TAC ex vars k `ek:byte list`;
     layout "mlkem_hash_h", API_HASH_H_SAFE_CALL_TAC ex vars;
     layout "mlkem_gen_matrix", EN_GM_SAFE_CALL_TAC ex vars k;
     layout "mlkem_hash_g", API_HASH_G_SAFE_CALL_TAC ex vars;
     layout "mlkem_getnoise", API_GETNOISE_SAFE_CALL_TAC ex vars;
     layout (nm ^ "_pke_encrypt"),
       API_PKE_SAFE_CALL_TAC ex vars "H_PE" [`X0`; `X1`; `X2`; `X3`; `X4`]] in
  let ef = 288 + 512 * (2 * k + 1) + 512 * k * k in
  let ninit = 1 + (if ef < 4096 then 1 else 2) + 6 + 4 + 2 in
  let derive = [layout(nm ^ "_enc_derand") + 4 * ninit,
                (fun _ -> MLKEM_NATIVE_ADRP_TAC)] in
  let setup =
    API_SAFE_ASSUME_TAC [] ["H_Z",zth] THEN
    ASSUME_CALLEE_TAILED_TAC MLKEM_CHECK_ENCODING_SUBROUTINE_FULL "H_CE" THEN
    ASSUME_CALLEE_TAILED_TAC MLKEM_HASH_H_SUBROUTINE_SAFE "H_HH" THEN
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
    MAP_EVERY X_GEN_TAC
     [`e:(uarch_event)list`; `ct:int64`; `ss:int64`; `pk:int64`;
      `coins:int64`; `ek:byte list`; `pc:num`] THEN
    WORD_FORALL_OFFSET_TAC (en_stack k) THEN
    MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
                C_RETURN; ALL; PAIRWISE; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
    REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
    SUBGOAL_THEN (parse_term("!i j. i < "^string_of_int k^" /\\ j < "^
       string_of_int k^" ==> mlkem_samplentt_terminates (APPEND ("^
       string_of_term(en_rho k)^") [word i; word j])"))
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
    ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
    MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
                (mk_const("X"^string_of_int n,[]))) (19--29) THEN
    ENSURES_INIT_TAC "s0"
  and finish =
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MEMACCESS_NUMERALS_TAC THEN NATIVE2_DISCHARGE_FRESH_TAC in
  setup,derive,calls,finish;;

let MLKEM_NATIVE2_ENC_DERAND_SAFE_TAC k ex gmth peth =
  let setup,derive,calls,finish = en_safe_parts k ex gmth peth in
  MLKEM_SAMPLENTT_TERMINATES_TAC (api_terminates_tm k (en_rho k) true)
   (setup THEN NATIVE2_SAFE_RUN_TAC ex derive calls 0 THEN
    API_BOOL_CASE_TAC (parse_term("mlkem_ek_check "^api_param k^" ek")) THEN
    ON_STATE(NATIVE2_SAFE_RUN_TAC ex derive calls) THEN finish);;

(* ------------------------------------------------------------------------- *)
(* dec: K-PKE.Decrypt, G, the matrix with H(ek) as a result, ek and h as     *)
(* variables for the events, the hash check and the case split on it; then   *)
(* K-PKE.Encrypt, the comparison and the selection.                          *)
(* ------------------------------------------------------------------------- *)

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

(*** rho as the slice of ek in dk, so that the events are those of ek ***)

let de_rho_ek k =
  list_mk_icomb "mlkem_slice"
   [mk_small_numeral(384 * k); `32`; `ek:byte list`];;

(*** gen_matrix by its theorem with H(ek) as a result: rho, ek at
 *** sk + 384 * k and the termination for the transposed matrix
 ***)

let DE_GM_SAFE_CALL_TAC exec vars k kk gl =
  let sp x = kp_spn x in
  let r c = find_read_fact c kk gl in
  let args =
    [r `X0`; r `X1`; de_rho_ek k; r `X4`; de_skoff(384 * k); `ek:byte list`;
     sp(de_hek k); sp(de_zc k); sp(de_j k); r `X5`] @
    (if k = 2 then [] else [sp(de_kr k + 32); sp(de_noise k)]) @
    [r `X6`; `pc:num`; r `SP`; r `X30`] in
  (API_SLICE_AT_TAC `sk:int64` `dk:byte list` (768 * k) 32 kk THEN
   API_SLICE_AT_TAC `sk:int64` `dk:byte list` (384 * k) (384 * k + 32) kk THEN
   RULE_ASSUM_TAC(REWRITE_RULE[GSYM(de_rho_eq k)]) THEN
   ABBREVS_TAC ["ek"; "h"] THEN
   API_CONSTS_TAC THEN
   API_SAFE_SIM_TAC exec vars "H_GM" args kk) gl;;

(*** The hash check at state kk: the digest and h as 64-bit words, the
 *** code, and the branch as H(ek) = h
 ***)

let DE_HASH_SAFE_BRANCH_TAC k kk =
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
    if can (term_match [] `read PC (s:armstate) = (x:int64)`) c &&
       rand(lhand c) = sv
    then
      let vt = find_term (can (term_match [] `val(x:int64) = 0`)) c in
      let eth = PART_MATCH (lhand o rand) WORD_OR_XOR_DIGITS_EQ_0 vt in
      let eth' = MP (CONV_RULE(RATOR_CONV(RAND_CONV NUM_REDUCE_CONV)) eth)
                    (CONJ (bnd hek) (bnd h)) in
      ASSUME_TAC(REWRITE_RULE[eth'; inj] th)
    else NO_TAC);;

let DE_DIGITS_TAC k kk =
  let sp x = kp_spn x in
  BIGDIGITS_32_TAC (sp(de_hek k)) `num_of_bytelist(sha3_256 ek)`
   (state_of kk) THEN
  API_SLICE_AT_TAC `sk:int64` `dk:byte list` (768 * k + 32) 32 kk THEN
  ABBREVS_TAC ["ek"; "h"] THEN
  BIGDIGITS_32_TAC (de_skoff(768 * k + 32)) `num_of_bytelist(h:byte list)`
   (state_of kk);;

(*** The proof of the safety of dec for k, with the safety theorems pdth
 *** and peth of pke_decrypt and pke_encrypt, as parts for debugging
 ***)

let de_safe_parts k ex gmth (pdth,peth) =
  let nm = api_param k and zl = de_zlen k in
  let zv = prove(api_zero_safe_tm (de_zv k) (de_zv k + 24) 96 zl,
                 API_ZERO_SAFE_TAC ex (de_zv k) 3 (de_zv k + 24) 96 zl)
  and zi = prove(api_zero_safe_tm (de_zi k) (de_zi k + 24) 96 zl,
                 API_ZERO_SAFE_TAC ex (de_zi k) 3 (de_zi k + 24) 96 zl) in
  let vars = [`ss:int64`; `ct:int64`; `sk:int64`; `pc:num`;
              `stackpointer:int64`; `returnaddress:int64`;
              `ek:byte list`; `h:byte list`] in
  let zil = [`e:(uarch_event)list`; `read SP s`; `pc:num`] in
  let calls =
    api_safe_calls ex vars [] [de_zv k,"H_ZV",zil; de_zi k,"H_ZI",zil] @
    [layout (nm ^ "_pke_decrypt"),
       API_PKE_SAFE_CALL_TAC ex vars "H_PD" [`X0`; `X1`; `X2`];
     layout "mlkem_hash_g", API_HASH_G_SAFE_CALL_TAC ex vars;
     layout "mlkem_gen_matrix",
       (fun kk -> DE_GM_SAFE_CALL_TAC ex vars k kk THEN
                  (if k = 2 then ALL_TAC else DE_DIGITS_TAC k (kk+1)));
     layout "mlkem_getnoise",
       (fun kk -> API_GETNOISE_SAFE_CALL_TAC ex vars kk THEN
                  DE_DIGITS_TAC k (kk+1));
     layout (nm ^ "_pke_encrypt"),
       API_PKE_SAFE_CALL_TAC ex vars "H_PE" [`X0`; `X1`; `X2`; `X3`; `X4`]]
  in
  let derive = [layout(nm ^ "_dec") + 4 * 14,
                (fun _ -> MLKEM_NATIVE_ADRP_TAC)] in
  let setup =
    API_SAFE_ASSUME_TAC [] ["H_ZV",zv; "H_ZI",zi] THEN
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
    MAP_EVERY X_GEN_TAC
     [`e:(uarch_event)list`; `ss:int64`; `ct:int64`; `sk:int64`;
      `dk:byte list`; `pc:num`] THEN
    WORD_FORALL_OFFSET_TAC (de_stack k) THEN
    MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
                C_RETURN; ALL; PAIRWISE; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
    REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
    SUBGOAL_THEN (parse_term("!i j. i < "^string_of_int k^" /\\ j < "^
       string_of_int k^" ==> mlkem_samplentt_terminates (APPEND ("^
       string_of_term(vsubst [de_ek k,`ek:byte list`] (de_rho_ek k))^
       ") [word i; word j])"))
    ASSUME_TAC THENL
     [REWRITE_TAC[de_rho_eq k] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    ASSUME_TAC(ISPECL [mk_small_numeral(384 * k);
                       mk_small_numeral(384 * k + 32); `dk:byte list`]
                      LENGTH_MLKEM_SLICE) THEN
    ASSUME_TAC(ISPECL [mk_small_numeral(768 * k + 32); `32`; `dk:byte list`]
                      LENGTH_MLKEM_SLICE) THEN
    ABBREV_TAC(mk_eq(`ek:byte list`,de_ek k)) THEN
    ABBREV_TAC(mk_eq(`h:byte list`,de_h k)) THEN
    ABBREVS_TAC ["ek"; "h"] THEN
    ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
    ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
    MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
                (mk_const("X"^string_of_int n,[]))) (19--29) THEN
    ENSURES_INIT_TAC "s0"
  and finish =
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MEMACCESS_NUMERALS_TAC THEN NATIVE2_DISCHARGE_FRESH_TAC in
  setup,derive,calls,finish;;

let MLKEM_NATIVE2_DEC_SAFE_TAC k ex gmth (pdth,peth) =
  let setup,derive,calls,finish = de_safe_parts k ex gmth (pdth,peth) in
  MLKEM_SAMPLENTT_TERMINATES_TAC (api_terminates_tm k (de_rho k) true)
   (setup THEN NATIVE2_SAFE_RUN_TAC ex derive calls 0 THEN
    ON_STATE(DE_HASH_SAFE_BRANCH_TAC k) THEN
    API_BOOL_CASE_TAC `sha3_256 ek = h` THEN
    ON_STATE(NATIVE2_SAFE_RUN_TAC ex derive calls) THEN finish);;
