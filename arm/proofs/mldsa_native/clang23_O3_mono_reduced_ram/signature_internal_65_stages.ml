(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The stages of an attempt of mldsa65_signature_internal (clang 23 -O3 mono *)
(* reduced-RAM), as FULL lemmas for segments of the code, in the structure   *)
(* of the 44 stages (signature_internal_44_stages.ml) with the region lemmas *)
(* of signature_internal_65_inline.ml. fp is the stack pointer after the     *)
(* prologue (aligned to 32); the callees use at most 1472 bytes below it, so *)
(* the frame of the stages is fp - 1472 .. fp + 12960.                       *)
(*                                                                           *)
(* The frame (offsets from fp): the rows of w at 3904 + 1024 k (k < 6), the  *)
(* product of a column at 544, z_i at 1856, the challenge (NTT) at 2880,     *)
(* w1 packed at 10048 + 128 k, the w1 (high parts) and the scratch           *)
(* polynomial at 10816, rho'' at 1792 (its pointer at 440 and 11840, kappa  *)
(* = 5 att at 416 (32 bits) and 11848 (16 bits)), the seed of A at 12160,   *)
(* the SHAKE256 states and buffers of the two samplings at 11936 to 12464,  *)
(* c~ at 11872, mu at 1728, the attempt counter at 76.                      *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/signature_internal_65_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/signature_internal_65_inline.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_ntt_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_uniform_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_challenge_65_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/H_65_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/lazy_eq_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_gamma1.ml";;
needs "arm/proofs/utils/mldsa_native_signing.ml";;
needs "arm/proofs/utils/mldsa_native_lazy_matrix.ml";;
needs "arm/proofs/utils/mldsa_native_libc.ml";;
needs "common/fips204/properties/mldsa_native_hints.ml";;
needs "arm/proofs/utils/mldsa_native_wrap.ml";;

let SI65_EXEC_RANGE lo hi =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   ([(layout ("mldsa65_signature_internal_" ^ lo),
      layout ("mldsa65_signature_internal_" ^ hi))] @
    [layout_range "plt_memcpy"; layout_range "plt_memset"]);;

(*** fp as fb_si + d in the goal and the assumptions, so that the memory    ***)
(*** safety checks compare regions with one base and no offsets that wrap  ***)

let SI65_FB_NORM_TAC d =
  let sub = WORD_RULE `word_sub (word_sub (x:int64) (word a)) (word b) =
                       word_sub x (word (a + b))` in
  let norm = REPEATC(CHANGED_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) in
  let dt = mk_small_numeral d in
  RULE_ASSUM_TAC(CONV_RULE(REWRITE_CONV[sub] THENC DEPTH_CONV NUM_ADD_CONV)) THEN
  REWRITE_TAC[sub] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  ABBREV_TAC (mk_eq(`fb_si:int64`,mk_comb(mk_comb(`word_sub:int64->int64->int64`,`fp:int64`),
                                          mk_comb(`word:num->int64`,dt)))) THEN
  SUBGOAL_THEN (mk_eq(`fp:int64`,mk_comb(mk_comb(`word_add:int64->int64->int64`,`fb_si:int64`),
                                        mk_comb(`word:num->int64`,dt)))) SUBST_ALL_TAC THENL
   [EXPAND_TAC "fb_si" THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  RULE_ASSUM_TAC(CONV_RULE norm) THEN CONV_TAC norm;;

let SI65_SAFETY_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  (CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]) THEN
  SI65_FB_NORM_TAC 1472 THEN
  REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN
  REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

(*** ASSUME_CALLEE_SAFETY_TAILED_TAC with the quantifiers rotated by a     ***)
(*** derived rule (MESON gives up beyond about ten variables)              ***)

let SI65_ASSUME_CALLEE_TAILED_TAC =
  let append_lemma = MESON[SAFETY_APPEND_EXISTS]
    `(forall (e:((A)address_uarch_event)list). P e) <=>
      (forall e_tail e. P (APPEND e_tail e))` in
  fun (safety_th:thm) (name:string) ->
    let th1 = ONCE_REWRITE_RULE[append_lemma] safety_th in
    let f,body = dest_exists (concl th1) in
    let args,_ = strip_forall body in
    let rot = tl args @ [hd args] in
    let th2 = GENL rot (SPECL args (ASSUME body)) in
    let th3 = EXISTS (mk_exists(f,concl th2),f) th2 in
    ASSUME_CALLEE_SAFETY_TAC (CHOOSE (f,th1) th3) name;;

(*** The GOT entries as the PLT code loads them: word_add (word pc) (word n) ***)

let SI65_GOT_TAC =
  W(fun (asl,w) ->
    MAP_EVERY (fun (_,th) ->
      let c = concl th in
      if is_eq c &&
         can (term_match [] `read (memory :> bytes64 (word (pc + n))) s`) (lhs c)
      then ASSUME_TAC(REWRITE_RULE[WORD_ADD] th) else ALL_TAC) asl);;

(*** A call of memset through the PLT, the BL being step n ***)

let SI65_MEMSET_TAC exec allowed n =
  LIBC_PLT_TAC exec n THEN
  G1_LIBC_CALL_TAC "H_MEMSET" exec
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`]
   allowed (n + 5);;

(*** Split on a boolean p, rewriting the other assumptions with it ***)

let SI65_CASES_TAC p =
  ASM_CASES_TAC p THEN
  FIRST_ASSUM(fun th -> if concl th = p || concl th = mk_neg p
    then RULE_ASSUM_TAC(fun th' -> if concl th' = concl th then th'
                                   else REWRITE_RULE[th] th')
    else NO_TAC);;

(*** The end of a stage: the frame (callees below fp) and the events ***)

let SI65_MAYCHANGE_TAC =
  W(fun (asl,w) -> if maychange_term w then ALL_TAC else NO_TAC) THEN
  SI65_FB_NORM_TAC 1472 THEN
  FIRST_X_ASSUM(fun th -> if maychange_term (concl th) && not(is_forall(concl th))
                          then MP_TAC th else NO_TAC) THEN
  DISCH_TAC THEN MONOTONE_MAYCHANGE_TAC;;

(*** From val fp + 12960 < 2^63 (the top of the frame does not wrap), the ***)
(*** bound val fp + n < 2^63 that a callee states (n <= 12960)             ***)

let SI65_FPB_TAC n =
  let tm = subst [mk_small_numeral n,`n:num`]
   `val (fp:int64) + 12960 < 2 EXP 63 ==> val fp + n < 2 EXP 63` in
  let th = ARITH_RULE tm in
  FIRST_ASSUM(fun ath -> if concl ath = lhand(concl th)
                         then ASSUME_TAC(MP th ath) else NO_TAC);;

let SI65_END_TAC = REPEAT CONJ_TAC THEN (SI65_MAYCHANGE_TAC ORELSE SI65_SAFETY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The cleanup of an attempt (CLEAN), from join12 with w21 = 1 on success    *)
(* and 0 otherwise: the memsets of z, c, w, w1 packed and the scratch        *)
(* polynomial, the zeroing of the rho'' pointer and kappa (fp + 11840) and   *)
(* of c~ (fp + 11872), and the test of w21: to loop2_exit2 on success, else  *)
(* to the next attempt (loop2, with the count att + 1 in w10) or, after the  *)
(* last (att = 13105), to loop2_exit1.                                       *)
(* ------------------------------------------------------------------------- *)

let SI65_CLEAN_STMT =
 `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e ok att fp pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 fp /\ att < 13106 /\
          ALL (nonoverlapping (word_sub fp (word 1472),14432))
              [(word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa65_signature_internal_join12) /\
                    read SP s = fp /\
                    read X21 s = (if ok then word 1 else word 0) /\
                    read (memory :> bytes32 (word_add fp (word 76))) s = word att /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read events s = e)
               (\s. read PC s =
                    (if ok then word (pc + mldsa65_signature_internal_loop2_exit2)
                     else if att + 1 < 13106
                     then word (pc + mldsa65_signature_internal_loop2)
                     else word (pc + mldsa65_signature_internal_loop2_exit1)) /\
                    read SP s = fp /\
                    (~ok ==> read X10 s = word (att + 1)) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (exists e2. read events s = APPEND e2 e /\
                       e2 = f_events ok att fp mf pc /\
                       memaccess_inbounds e2
                        [word_sub fp (word 1472),14432; word(pc + got_memset),8; ea,el]
                        [word_sub fp (word 1472),14432]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
                MAYCHANGE [memory :> bytes(word_add fp (word 1856),1024);
                           memory :> bytes(word_add fp (word 2880),1024);
                           memory :> bytes(word_add fp (word 3904),6144);
                           memory :> bytes(word_add fp (word 10048),768);
                           memory :> bytes(word_add fp (word 10816),1024);
                           memory :> bytes(word_add fp (word 11840),16);
                           memory :> bytes(word_add fp (word 11872),48)])`;;

let SI65_CLEAN_EXEC = SI65_EXEC_RANGE "join12" "loop2_exit1";;

(*** The test of the count of the attempts (cmp w8, w9 = 13104; b.ls) and ***)
(*** the next count                                                       ***)

let SI65_ATT_TEST = prove
 (`!att. att < 13106
         ==> (~(&(val (word att:int32)) - &13104:int =
                &(val (word_sub (word att:int32) (word 13104))) /\
                ~(val (word_sub (word att:int32) (word 13104)) = 0)) <=>
              att + 1 < 13106)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`word att:int32`; `13104`] GLUE_FLAGS_LS) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `att MOD 4294967296 = att` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let SI65_ATT_INC = prove
 (`!att. att < 13106
         ==> word_zx (word_add (word att:int32) (word 1)):int64 = word (att + 1)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD; DIMINDEX_32;
              DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `att MOD 4294967296 = att /\ (att + 1) MOD 4294967296 = att + 1 /\
                (att + 1) MOD 18446744073709551616 = att + 1` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_REWRITE_TAC[]]);;

let SI65_CLEAN = prove
 (SI65_CLEAN_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[memset_full_contract] th) "H_MEMSET") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(ok:bool) (att:num) (fp:int64) (mf:int64) (pc:num).
      if ok then f_ev_ok fp mf pc
      else if att + 1 < 13106 then f_ev_nx fp mf pc
      else f_ev_ex fp mf pc:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `ok:bool`; `att:num`; `fp:int64`;
                       `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; fst SI65_CLEAN_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN SI65_GOT_TAC THEN
  (let ms = SI65_MEMSET_TAC SI65_CLEAN_EXEC [`fp:int64`; `mf:int64`; `pc:num`] in
   ARM_STEPS_TAC SI65_CLEAN_EXEC (1--4) THEN ms 4 THEN
   ARM_STEPS_TAC SI65_CLEAN_EXEC (10--13) THEN ms 13 THEN
   ARM_STEPS_TAC SI65_CLEAN_EXEC (19--23) THEN ms 23 THEN
   ARM_STEPS_TAC SI65_CLEAN_EXEC (29--33) THEN ms 33 THEN
   ARM_STEPS_TAC SI65_CLEAN_EXEC (39--45) THEN ms 45 THEN
   ARM_STEPS_TAC SI65_CLEAN_EXEC (51--61)) THEN
  SI65_CASES_TAC `ok:bool` THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV WORD_RED_CONV)) THEN ASM_REWRITE_TAC[] THENL
   [ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SI65_SAFETY_TAC;
    ALL_TAC] THEN
  ARM_STEPS_TAC SI65_CLEAN_EXEC (62--66) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `att:num` SI65_ATT_TEST) (ASSUME `att < 13106`);
    MP (SPEC `att:num` SI65_ATT_INC) (ASSUME `att < 13106`)]) THEN
  SI65_CASES_TAC `att + 1 < 13106` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SI65_SAFETY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The packing of c~ and of the hints (TAIL), from the exit of the loop over *)
(* the rows (loop45_exit1): for each row k the w1 unpacking SI65_W1U (row 0  *)
(* also copies c~ (48 bytes at fp + 11872) to sig and zeroes the 61 bytes of *)
(* the hints; rows 1 to 5 store the count of the row before at sig + 3302 + *)
(* k) and the hint loop SI65_HROW. If the hints fit, the code stores the    *)
(* last count, sets w21 to 1 and goes to the cleanup at join12 with the     *)
(* hints of mld_pack_hints at sig + 3248; otherwise it goes there through   *)
(* join9 with w21 = 0.                                                       *)
(* ------------------------------------------------------------------------- *)

let SI65_SLOT_FACTS l = String.concat "" (map (fun (a,v) ->
  Printf.sprintf
   "read (memory :> bytes64 (word_add fp (word %d))) s = word_add fp (word %d) /\\\n" a v) l);;

let SI65_H = `mld_polyvec_make_hint_32 x b`;;

let SI65_TAIL_STMT = parse_term(
 "exists f_events.
    forall e sig fp (C:num) (x:num->int32) (b:num->byte) pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 16 fp /\\
      nonoverlapping (sig,3309) (word_sub fp (word 1472),14432) /\\
      ALL (nonoverlapping (word pc,libmldsa_size))
          [(sig,3309); (word_sub fp (word 1472),14432)]
      ==> ensures arm
           (\\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read PC s = word (pc + mldsa65_signature_internal_loop45_exit1) /\\
                read SP s = fp /\\
                read X20 s = word_add fp (word 10816) /\\
                read X25 s = word_add fp (word 3904) /\\
                read X24 s = word 523777 /\\
                read Q17 s = " ^ SI65_MASK ^ " /\\
                read (memory :> bytes64 (word_add fp (word 64))) s = sig /\\
                read (memory :> bytes64 (word_add fp (word 16))) s =
                word_add sig (word 3248) /\\\n" ^
  SI65_SLOT_FACTS [24,8000; 32,6976; 40,5952; 48,4928; 344,9024] ^
 "              read (memory :> bytes (word_add fp (word 11872),48)) s = C /\\
                (!j. j < 1536 ==> read (memory :> bytes32 (word_add fp (word (3904 + 4 * j)))) s = x j) /\\
                (!j. j < 768 ==> read (memory :> bytes8 (word_add fp (word (10048 + j)))) s = b j) /\\
                read events s = e)
           (\\s. read PC s = word (pc + mldsa65_signature_internal_join12) /\\
                read SP s = fp /\\
                read X21 s =
                (if mld_hint_count (mld_polyvec_make_hint_32 x b) 1536 <= 55
                 then word 1 else word 0) /\\
                read (memory :> bytes (sig,48)) s = C /\\
                (mld_hint_count (mld_polyvec_make_hint_32 x b) 1536 <= 55
                 ==> !t. t < 61
                         ==> read (memory :> bytes8 (word_add sig (word (3248 + t)))) s =
                             mld_pack_hints 55 6 (mld_polyvec_make_hint_32 x b) t) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events sig fp pc x b /\\
                   memaccess_inbounds e2
                    [sig,3309; word_sub fp (word 1472),14432]
                    [sig,3309; word_sub fp (word 1472),14432]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
            MAYCHANGE [X21; X22] ,,
            MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
            MAYCHANGE [memory :> bytes(sig,48);
                       memory :> bytes(word_add sig (word 3248),61);
                       memory :> bytes(word_add fp (word 10816),1024)])");;

let SI65_TAIL_EXEC = SI65_EXEC_RANGE "loop45_exit1" "loop2_exit2";;

let SI65_TL_TEMPLATE =
 `\(sig:int64) (fp:int64) (pc:num) (x:num->int32) (b:num->byte).
   if mld_hint_count (mld_polyvec_make_hint_32 x b) 256 <= 55 then
   (if mld_hint_count (mld_polyvec_make_hint_32 x b) 512 <= 55 then
    (if mld_hint_count (mld_polyvec_make_hint_32 x b) 768 <= 55 then
     (if mld_hint_count (mld_polyvec_make_hint_32 x b) 1024 <= 55 then
      (if mld_hint_count (mld_polyvec_make_hint_32 x b) 1280 <= 55 then
       (if mld_hint_count (mld_polyvec_make_hint_32 x b) 1536 <= 55
        then f_ev_ok sig fp pc x b else f_ev_r5 sig fp pc x b)
       else f_ev_r4 sig fp pc x b)
      else f_ev_r3 sig fp pc x b)
     else f_ev_r2 sig fp pc x b)
    else f_ev_r1 sig fp pc x b)
   else f_ev_r0 sig fp pc x b :(uarch_event)list`;;

let SI65_TL_ALLOWED = [`sig:int64`; `fp:int64`; `pc:num`; `x:num->int32`; `b:num->byte`];;

let SI65_TL_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc SI65_TAIL_EXEC
    name ilist SI65_TL_ALLOWED n;;

(*** The facts for row k of b and of x at state n ***)

let SI65_TL_B_SLICE_TAC k n =
  let ib = 10048 + 128 * k and wb = 128 * k in
  let st = mk_var("s"^string_of_int n,`:armstate`) in
  SUBGOAL_THEN (vsubst [st,`s:armstate`] (parse_term(Printf.sprintf
    "!j. j < 128 ==> read (memory :> bytes8 (word_add fp (word (%d + j)))) s =
                     (b:num->byte) (%d + j)" ib wb)))
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC (parse_term(Printf.sprintf "%d + j" wb)) o check (fun th ->
      is_forall(concl th) && can (term_match []
       `!j. j < 768 ==> read (memory :> bytes8 (word_add fp (word (10048 + j)))) s = b j`)
       (concl th))) THEN
    REWRITE_TAC[ARITH_RULE(parse_term(Printf.sprintf "10048 + %d + j = %d + j" wb ib))] THEN
    DISCH_THEN MATCH_MP_TAC THEN UNDISCH_TAC `j < 128` THEN ARITH_TAC;
    ALL_TAC];;

let SI65_TL_X_SLICE_TAC k n =
  let w = 3904 + 1024 * k and p0 = 256 * k in
  let st = mk_var("s"^string_of_int n,`:armstate`) in
  SUBGOAL_THEN (vsubst [st,`s:armstate`] (parse_term(Printf.sprintf
    "!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (%d + 4 * i)))) s = x (%d + i)" w p0)))
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC (parse_term(Printf.sprintf "%d + i" p0)) o check (fun th ->
      is_forall(concl th) && can (term_match []
       `!j. j < 1536 ==> read (memory :> bytes32 (word_add fp (word (3904 + 4 * j)))) s = x j`)
       (concl th))) THEN
    REWRITE_TAC[ARITH_RULE(parse_term(Printf.sprintf "3904 + 4 * (%d + i) = %d + 4 * i" p0 w))] THEN
    DISCH_THEN MATCH_MP_TAC THEN UNDISCH_TAC `i < 256` THEN ARITH_TAC;
    ALL_TAC];;

let SI65_TL_CNT_TM p = subst [mk_small_numeral p,`p:num`]
  `mld_hint_count (mld_polyvec_make_hint_32 x b) p <= 55`;;

let SI65_TL_SPLIT_TAC p =
  let c = SI65_TL_CNT_TM p in
  ASM_CASES_TAC c THEN
  FIRST_ASSUM(fun th -> if concl th = c || concl th = mk_neg c
    then RULE_ASSUM_TAC(fun th' -> if concl th' = concl th then th' else REWRITE_RULE[th] th')
    else NO_TAC) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && free_in `X8` (concl th)
                                then STRIP_ASSUME_TAC th else NO_TAC));;

(*** A hint that does not fit: through join9 (2 instructions from step n) ***)

let SI65_TL_FAIL_TAC p n =
  SUBGOAL_THEN (mk_neg(SI65_TL_CNT_TM 1536)) ASSUME_TAC THENL
   [MP_TAC(SPECL [`mld_polyvec_make_hint_32 x b`; mk_small_numeral p; `1536`]
                 MLD_HINT_COUNT_MONO) THEN
    FIRST_ASSUM(MP_TAC o check (fun th -> concl th = mk_neg(SI65_TL_CNT_TM p))) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ARM_STEPS_TAC SI65_TAIL_EXEC (n--(n+1)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SI65_SAFETY_TAC;;

let SI65_ZX_BYTE = prove
 (`!n. word_zx (word_zx (word n:int64):int32):byte = word n`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_32;
              DIMINDEX_64] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

let SI65_TL_PACK_TAC =
  X_GEN_TAC `t:num` THEN DISCH_TAC THEN REWRITE_TAC[mld_pack_hints] THEN
  CONV_TAC NUM_REDUCE_CONV THEN COND_CASES_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    SUBGOAL_THEN `t = 55 \/ t = 56 \/ t = 57 \/ t = 58 \/ t = 59 \/ t = 60` MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`t < 61`; `~(t < 55)`] THEN ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[SI65_ZX_BYTE]];;

let SI65_TL_COUNT0_TAC =
  ASSUME_TAC(INST [`mld_polyvec_make_hint_32 x b`,`h:num->bool`]
                  (CONJUNCT1 mld_hint_count)) THEN
  ASSUME_TAC(ARITH_RULE `0 <= 55`);;

(*** Row k (1 to 5) from step n (the HROW of the row before): the w1 unpack ***)
(*** of the row (step n + 1), the hint loop (n + 2), the split on the count ***)

let SI65_TL_ROW_TAC k n =
  let p0 = 256 * k and p1 = 256 * (k + 1) in
  SI65_TL_B_SLICE_TAC k n THEN
  SI65_TL_CALL_TAC ("H_W1U"^string_of_int k)
   [`fp:int64`; parse_term(Printf.sprintf "\\t. (b:num->byte) (%d + t)" (128 * k));
    `sig:int64`;
    parse_term(Printf.sprintf "mld_hint_count (mld_polyvec_make_hint_32 x b) %d" p0);
    `pc:num`] (n + 1) THEN
  SI65_TL_X_SLICE_TAC k (n + 1) THEN
  SI65_TL_CALL_TAC ("H_HROW"^string_of_int k)
   [`x:num->int32`; `b:num->byte`; `sig:int64`; `fp:int64`; `pc:num`] (n + 2) THEN
  SI65_TL_SPLIT_TAC p1 THENL [ALL_TAC; SI65_TL_FAIL_TAC p1 (n + 3)];;

let SI65_TAIL = prove
 (SI65_TAIL_STMT,
  MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
   (zip (SI65_W1U0 :: SI65_W1UK)
        ["H_W1U0"; "H_W1U1"; "H_W1U2"; "H_W1U3"; "H_W1U4"; "H_W1U5"] @
    zip SI65_HROW ["H_HROW0"; "H_HROW1"; "H_HROW2"; "H_HROW3"; "H_HROW4"; "H_HROW5"]) THEN
  CONCRETIZE_F_EVENTS_TAC SI65_TL_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `sig:int64`; `fp:int64`; `C:num`;
                       `x:num->int32`; `b:num->byte`; `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; fst SI65_TAIL_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN
  MAP_EVERY (fun n ->
    MP_TAC(SPECL [`word_add fp (word 11872):int64`; `48`; `C:num`; mk_small_numeral n;
                  `s0:armstate`] SIGN_BYTES128_OF_BYTES) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC) [0;1;2] THEN
  (*** row 0, with the copy of c~ and the zero hints ***)
  SI65_TL_B_SLICE_TAC 0 0 THEN
  SI65_TL_CALL_TAC "H_W1U0"
   ([`fp:int64`; `\t. (b:num->byte) (0 + t)`; `sig:int64`] @
    map (fun k -> mk_comb(`word:num->int128`, rhs(concl(NUM_REDUCE_CONV
      (subst [mk_small_numeral k,`k:num`] `(C DIV 2 EXP (128 * k)) MOD 2 EXP 128`)))))
     [0;1;2] @ [`pc:num`]) 1 THEN
  (*** sig[0,48) = C ***)
  SUBGOAL_THEN `C < 2 EXP (8 * 48)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if can (term_match []
       `read (memory :> bytes (word_add fp (word 11872),48)) s0 = C`) (concl th)
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[READ_BYTES_BOUND; READ_COMPONENT_COMPOSE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`sig:int64`; `C:num`; `3`; `s1:armstate`] SIGN_BYTES_OF_BYTES128) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0; DIV_1] THEN ASM_REWRITE_TAC[DIV_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `C MOD 2 EXP (128 * 3) = C` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN
    FIRST_ASSUM(MP_TAC o check (fun th -> concl th = `C < 2 EXP (8 * 48)`)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN DISCH_TAC THEN
  SUBGOAL_THEN `!t. t < 55 ==> read (memory :> bytes8 (word_add sig (word (3248 + t)))) s1 =
                              mld_hint_index (mld_polyvec_make_hint_32 x b) 0 t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[CONJUNCT1 mld_hint_index] THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && can (term_match []
        `!t. t < 61 ==> read (memory :> bytes8 (word_add sig (word (3248 + t)))) s = y t`)
        (concl th))) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SI65_TL_X_SLICE_TAC 0 1 THEN SI65_TL_COUNT0_TAC THEN
  SI65_TL_CALL_TAC "H_HROW0"
   [`x:num->int32`; `b:num->byte`; `sig:int64`; `fp:int64`; `pc:num`] 2 THEN
  SI65_TL_SPLIT_TAC 256 THENL [ALL_TAC; SI65_TL_FAIL_TAC 256 3] THEN
  (*** rows 1 to 5, and the success ***)
  SI65_TL_ROW_TAC 1 2 THEN SI65_TL_ROW_TAC 2 4 THEN SI65_TL_ROW_TAC 3 6 THEN
  SI65_TL_ROW_TAC 4 8 THEN SI65_TL_ROW_TAC 5 10 THEN
  ARM_STEPS_TAC SI65_TAIL_EXEC (13--16) THEN ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [SI65_TL_PACK_TAC; SI65_SAFETY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* s2 and t0 in the NTT domain, from the secret key skb, as the row          *)
(* iterations unpack and transform them, polynomial by polynomial.          *)
(* ------------------------------------------------------------------------- *)

let SI65_S2U =
 `mld_polyvec_unpack 128 mld_polyeta_unpack_4 (\j. (skb:num->byte)(768 + j))`;;
let SI65_S2H = mk_comb(`mld_polyvec_map mld_poly_ntt`,SI65_S2U);;
let SI65_T0U =
 `mld_polyvec_unpack 416 mld_polyt0_unpack (\j. (skb:num->byte)(1536 + j))`;;
let SI65_T0H = mk_comb(`mld_polyvec_map mld_poly_ntt`,SI65_T0U);;

(* ------------------------------------------------------------------------- *)
(* One iteration of the loop over the rows of w0 (RIT), from loop45 with row *)
(* j in x22: s2_j unpacked into the scratch polynomial at fp + 10816 and     *)
(* transformed, its product with the challenge, w0_j - c s2_j in place and   *)
(* reduced, its norm check; then t0_j likewise, c t0_j reduced and checked, *)
(* and the sum in place in row j. ok1 and ok2 are the results of the two     *)
(* checks: if both pass, the code goes back to loop45 or, after the last row, *)
(* to loop45_exit1, else to the rejection at join10.                         *)
(* ------------------------------------------------------------------------- *)

let SI65_RIT_R0 = list_mk_comb(`mld_sign_r0`,
  [`mld_poly_decompose_lo_32`; `w:num->int32`; SI65_S2H; `cphat:num->int32`; `j:num`]);;
let SI65_RIT_CT0 = list_mk_comb(`mld_sign_ct0`, [SI65_T0H; `cphat:num->int32`; `j:num`]);;

let SI65_FOUR = "word 0x00000004000000040000000400000004";;

let SI65_PAGE_FACTS rs = String.concat "" (map (fun r ->
  "read " ^ r ^ " s = word_add (word pc) (word 245760) /\\\n") rs);;

let SI65_RIT_CONST =
  "read Q17 s = " ^ SI65_MASK ^ " /\\ read Q16 s = " ^ SI65_FOUR ^ " /\\\n" ^
  SI65_PAGE_FACTS ["X15";"X16";"X17";"X18"];;

let SI65_RIT_PRE =
 "read SP s = fp /\\
  read X20 s = word_add fp (word 10816) /\\
  read X26 s = word 18446744073701171199 /\\ read X19 s = word 252236767799803904 /\\
  read X28 s = word_add fp (word 10824) /\\
  read (memory :> bytes64 (word_add fp (word 320))) s = word_add fp (word 2888) /\\
  read (memory :> bytes64 (word_add fp (word 448))) s = word_add sk (word 768) /\\
  read (memory :> bytes64 (word_add fp (word 480))) s = word_add sk (word 1536) /\\
  read (memory :> bytes128 (word_add fp (word 368))) s =
  word 339618401959998730991157055895298383871 /\\
  (!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (2880 + 4 * i)))) s =
                   cphat i) /\\
  (!i. i < 4032 ==> read (memory :> bytes8 (word_add sk (word i))) s = skb i)";;

let SI65_RIT_ROW j =
  Printf.sprintf
  "read X22 s = word %s /\\ read X12 s = word (128 * %s) /\\
   read X21 s = word_add fp (word (3920 + 1024 * %s)) /\\
   read X23 s = word_add fp (word (3904 + 1024 * %s)) /\\
   read (memory :> bytes64 (word_add fp (word 416))) s = word (6 + 416 * %s) /\\\n"
  j j j j j;;

let SI65_RIT_STMT = parse_term(
 "exists f_events.
    forall e ok1 ok2 sk skb fp j w cphat pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 16 fp /\\ val fp + 12960 < 2 EXP 63 /\\ j < 6 /\\
      (ok1 <=> mld_poly_chknorm (" ^ string_of_term SI65_RIT_R0 ^ ") (word 261692) = word 0) /\\
      (ok1 ==> (ok2 <=> mld_poly_chknorm (" ^ string_of_term SI65_RIT_CT0 ^ ") (word 261888) =
                        word 0)) /\\
      ALL (nonoverlapping (word_sub fp (word 1472),14432))
          [(sk,4032); (word pc,libmldsa_size)]
      ==> ensures arm
           (\\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read PC s = word (pc + mldsa65_signature_internal_loop45) /\\\n" ^
  SI65_RIT_ROW "j" ^ SI65_RIT_CONST ^ SI65_RIT_PRE ^ " /\\
                (!i. i < 256 ==> read (memory :> bytes32
                                   (word_add fp (word ((3904 + 1024 * j) + 4 * i)))) s =
                                 mld_poly_decompose_lo_32 (mld_poly_of w j) i) /\\
                read events s = e)
           (\\s. read PC s =
                (if ok1 /\\ ok2
                 then (if j + 1 < 6 then word (pc + mldsa65_signature_internal_loop45)
                       else word (pc + mldsa65_signature_internal_loop45_exit1))
                 else word (pc + mldsa65_signature_internal_join10)) /\\
                read SP s = fp /\\
                (ok1 /\\ ok2
                 ==> " ^ SI65_RIT_ROW "(j + 1)" ^ SI65_RIT_CONST ^
 "                   read X25 s = word_add fp (word 3904) /\\
                     (!i. i < 256 ==> read (memory :> bytes32
                                        (word_add fp (word ((3904 + 1024 * j) + 4 * i)))) s =
                                      mld_poly_add (" ^ string_of_term SI65_RIT_R0 ^ ")
                                                   (" ^ string_of_term SI65_RIT_CT0 ^ ") i)) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events ok1 ok2 sk fp j pc /\\
                   memaccess_inbounds e2
                    [sk,4032; word_sub fp (word 1472),14432;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa65_signature_internal_consts),336]
                    [word_sub fp (word 1472),14432]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [X18; X21; X22; X23; X25; X27; X30] ,,
            MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
            MAYCHANGE [memory :> bytes(word_sub fp (word 208),208);
                       memory :> bytes(word_add fp (word 416),8);
                       memory :> bytes(word_add fp (word (3904 + 1024 * j)),1024);
                       memory :> bytes(word_add fp (word 10816),1024)])");;

let SI65_RIT_EXEC = SI65_EXEC_RANGE "loop45" "loop45_exit1";;

let SI65_RIT_TEMPLATE =
 `\(ok1:bool) (ok2:bool) (sk:int64) (fp:int64) (j:num) (pc:num).
   if ok1 then
    (if ok2 then (if j + 1 < 6 then f_ev_mid sk fp j pc else f_ev_last sk fp j pc)
     else f_ev_f2 sk fp j pc)
   else f_ev_f1 sk fp j pc :(uarch_event)list`;;

let SI65_RIT_ALLOWED = [`ok1:bool`; `ok2:bool`; `sk:int64`; `fp:int64`; `j:num`; `pc:num`];;

let SI65_RIT_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc SI65_RIT_EXEC
    name ilist SI65_RIT_ALLOWED n;;

(*** Bytes aoff + k of the secret key at state st, as voff + k ***)

let SI65_SK_SLICE_TAC aoff voff n st =
  let t = vsubst [st,`s:armstate`] (parse_term(Printf.sprintf
   "!k. k < %d ==> read (memory :> bytes8 (word_add sk (word (%s + k)))) s =
                   (skb:num->byte) (%s + k)" n aoff voff)) in
  SUBGOAL_THEN t ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (term_match []
       `!i. i < 4032 ==> read (memory :> bytes8 (word_add sk (word i))) s = skb i`)
       (concl th))) THEN
    MAP_EVERY UNDISCH_TAC [`j < 6`; mk_binop `(<):num->num->bool` `k:num` (mk_small_numeral n)] THEN
    ARITH_TAC;
    ALL_TAC];;

(*** A register fact restated in the form a precondition needs (state n) ***)

let SI65_REG_FORM_TAC reg n (nw:term) =
  let s = mk_var("s"^string_of_int n,`:armstate`) in
  let lh = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                           mk_const(reg,[])),s) in
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = lh
    then let tm = mk_eq(rhs(concl th),nw) in
         let eth = try prove(tm, CONV_TAC(DEPTH_CONV WORD_RED_CONV))
                   with Failure _ -> WORD_RULE tm in
         ASSUME_TAC(TRANS th eth) else NO_TAC);;

(*** The checks as (P <=> ok), and the branch on a check (cbnz w8) as ok ***)

let SI65_ORIENT_TAC =
  FIRST_X_ASSUM(fun th -> if is_iff(concl th) && lhs(concl th) = `ok1:bool`
                          then ASSUME_TAC(GSYM th) else NO_TAC) THEN
  FIRST_X_ASSUM(fun th -> if is_imp(concl th) && lhand(concl th) = `ok1:bool`
                          then ASSUME_TAC(CONV_RULE(RAND_CONV SYM_CONV) th) else NO_TAC);;

let SI65_DECIDE_TAC okv =
  FIRST_X_ASSUM(fun th ->
    if is_iff(concl th) && rhs(concl th) = okv then
      RULE_ASSUM_TAC(fun th' ->
        if can (term_match [] `read PC s = x`) (concl th') ||
           can (term_match [] `read events s = x`) (concl th')
        then REWRITE_RULE[th] (REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0] th')
        else th')
    else NO_TAC);;

let SI65_RIT_FAIL_TAC okv =
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read PC s = x`) (concl th)
                           then REWRITE_RULE[ASSUME(mk_neg okv)] th else th) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SI65_END_TAC;;

let SI65_RIT_POLY v = mk_comb(mk_comb(`mld_poly_of`,v),`j:num`);;
let SI65_RIT_PW1 = list_mk_comb(`mld_poly_pointwise_montgomery`,
  [SI65_RIT_POLY SI65_S2H; `cphat:num->int32`]);;
let SI65_RIT_PW2 = list_mk_comb(`mld_poly_pointwise_montgomery`,
  [SI65_RIT_POLY SI65_T0H; `cphat:num->int32`]);;
let SI65_RIT_CS2 = mk_comb(`mld_poly_invntt_tomont`,SI65_RIT_PW1);;
let SI65_RIT_W0J = `mld_poly_decompose_lo_32 (mld_poly_of (w:num->int32) j)`;;
let SI65_RIT_SUBX = list_mk_comb(`mld_poly_sub`,[SI65_RIT_W0J; SI65_RIT_CS2]);;

let SI65_LK l name =
  try assoc name l with Failure _ -> assoc ("mldsa65_signature_internal_" ^ name) l;;

let SI65_RIT_CALLEES () =
  [SI65_ETA_R,"H_ETA"; snd(hd SI65_T0UNP),"H_T0U";
   MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_NTT";
   MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_INV";
   SI65_LK SI65_PWM "loop48","H_PWM48"; SI65_LK SI65_PWM "loop52","H_PWM52";
   SI65_RSUB,"H_RSUB"; SI65_LK SI65_RED "loop49","H_RED49";
   SI65_LK SI65_CHK "loop50","H_CHK50"; SI65_LK SI65_RED "loop53","H_RED53";
   SI65_LK SI65_CHK "loop54","H_CHK54"; SI65_RADD,"H_RADD"];;

(*** From loop45 to the first check (step 22) ***)

let SI65_RIT_PART1_TAC =
  SI65_SK_SLICE_TAC "768 + 128 * j" "768 + 128 * j" 128 `s0:armstate` THEN
  SUBGOAL_THEN `j < 8` ASSUME_TAC THENL [UNDISCH_TAC `j < 6` THEN ARITH_TAC; ALL_TAC] THEN
  SI65_RIT_CALL_TAC "H_ETA" [`fp:int64`; `word_add sk (word 768):int64`; `j:num`;
    `\k. (skb:num->byte) (768 + 128 * j + k)`; `pc:num`] 1 THEN
  MLD_LAZY_REPOLY_TAC `mld_polyeta_unpack_4 (\k. (skb:num->byte) (768 + 128 * j + k))`
    (SI65_RIT_POLY SI65_S2U) [mld_polyvec_unpack; MLD_POLY_OF_POLYVEC] THEN
  ARM_STEPS_TAC SI65_RIT_EXEC (2--4) THEN
  SI65_RIT_CALL_TAC "H_NTT" [`read X0 s`; SI65_RIT_POLY SI65_S2U; `pc:num`;
                              `read SP s`; `read X30 s`] 5 THEN
  MLD_LAZY_REPOLY_TAC (mk_comb(`mld_poly_ntt`,SI65_RIT_POLY SI65_S2U))
    (SI65_RIT_POLY SI65_S2H) [MLD_POLY_OF_POLYVEC_MAP] THEN
  ARM_STEPS_TAC SI65_RIT_EXEC (6--8) THEN
  SI65_RIT_CALL_TAC "H_PWM48" [`word_add fp (word 10816):int64`;
    `word_add fp (word 2880):int64`; SI65_RIT_POLY SI65_S2H; `cphat:num->int32`;
    `pc:num`] 9 THEN
  ARM_STEPS_TAC SI65_RIT_EXEC (10--12) THEN
  SI65_RIT_CALL_TAC "H_INV" [`read X0 s`; SI65_RIT_PW1; `pc:num`; `read SP s`;
                              `read X30 s`] 13 THEN
  ARM_STEPS_TAC SI65_RIT_EXEC [14] THEN
  SI65_RIT_CALL_TAC "H_RSUB" [`fp:int64`; `word_add fp (word (3904 + 1024 * j)):int64`;
    SI65_RIT_W0J; SI65_RIT_CS2; `j:num`; `word_add fp (word (3920 + 1024 * j)):int64`;
    `pc:num`] 15 THEN
  SI65_REG_FORM_TAC "X8" 15 `word_add fp (word ((3904 + 1024 * j) + 16)):int64` THEN
  SI65_RIT_CALL_TAC "H_RED49" [`word_add fp (word (3904 + 1024 * j)):int64`;
    SI65_RIT_SUBX; `pc:num`] 16 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_r0]) THEN
  ARM_STEPS_TAC SI65_RIT_EXEC (17--20) THEN
  SI65_REG_FORM_TAC "X13" 20 `word_zx (word_sub (word 261692:int32) (word 1)):int64` THEN
  SI65_REG_FORM_TAC "X8" 20 `word_zx (word 0:int32):int64` THEN
  SI65_RIT_CALL_TAC "H_CHK50" [`word_add fp (word (3904 + 1024 * j)):int64`;
    SI65_RIT_R0; `word 261692:int32`; `word 0:int32`; `pc:num`] 21 THEN
  ARM_STEPS_TAC SI65_RIT_EXEC [22] THEN
  SI65_DECIDE_TAC `ok1:bool` THEN SI65_CASES_TAC `ok1:bool` THENL
   [ALL_TAC; SI65_RIT_FAIL_TAC `ok1:bool`];;

(*** Steps that are ADRPs, each normalized ***)

let SI65_ADRP_STEPS_TAC exec ns =
  MAP_EVERY (fun n -> ARM_STEPS_TAC exec [n] THEN MLKEM_NATIVE_ADRP_TAC) ns;;

(*** From the first check to the second (step 54) ***)

let SI65_RIT_PART2_TAC =
  ARM_STEPS_TAC SI65_RIT_EXEC (23--26) THEN
  SI65_REG_FORM_TAC "X9" 26 `word_add sk (word ((1536 + 416 * j) + 6)):int64` THEN
  SI65_SK_SLICE_TAC "(1536 + 416 * j)" "1536 + 416 * j" 416 `s26:armstate` THEN
  SI65_RIT_CALL_TAC "H_T0U" [`word_add fp (word 10816):int64`;
    `word_add sk (word (1536 + 416 * j)):int64`;
    `\k. (skb:num->byte) (1536 + 416 * j + k)`; `pc:num`] 27 THEN
  MLD_LAZY_REPOLY_TAC `mld_polyt0_unpack (\k. (skb:num->byte) (1536 + 416 * j + k))`
    (SI65_RIT_POLY SI65_T0U) [mld_polyvec_unpack; MLD_POLY_OF_POLYVEC] THEN
  ARM_STEPS_TAC SI65_RIT_EXEC (28--30) THEN
  SI65_RIT_CALL_TAC "H_NTT" [`read X0 s`; SI65_RIT_POLY SI65_T0U; `pc:num`;
                              `read SP s`; `read X30 s`] 31 THEN
  MLD_LAZY_REPOLY_TAC (mk_comb(`mld_poly_ntt`,SI65_RIT_POLY SI65_T0U))
    (SI65_RIT_POLY SI65_T0H) [MLD_POLY_OF_POLYVEC_MAP] THEN
  ARM_STEPS_TAC SI65_RIT_EXEC (32--34) THEN
  SI65_RIT_CALL_TAC "H_PWM52" [`word_add fp (word 10816):int64`;
    `word_add fp (word 2880):int64`; SI65_RIT_POLY SI65_T0H; `cphat:num->int32`;
    `pc:num`] 35 THEN
  ARM_STEPS_TAC SI65_RIT_EXEC (36--38) THEN
  SI65_RIT_CALL_TAC "H_INV" [`read X0 s`; SI65_RIT_PW2; `pc:num`; `read SP s`;
                              `read X30 s`] 39 THEN
  ARM_STEPS_TAC SI65_RIT_EXEC (40--42) THEN
  SI65_RIT_CALL_TAC "H_RED53" [`word_add fp (word 10816):int64`;
    mk_comb(`mld_poly_invntt_tomont`,SI65_RIT_PW2); `pc:num`] 43 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_ct0]) THEN
  ARM_STEPS_TAC SI65_RIT_EXEC (44--48) THEN
  SI65_ADRP_STEPS_TAC SI65_RIT_EXEC (49--52) THEN
  SI65_REG_FORM_TAC "X13" 52
    `word_zx (word_sub (word_sub (word 261888:int32) (word 1)) (word 196)):int64` THEN
  SI65_REG_FORM_TAC "X8" 52 `word_zx (word 0:int32):int64` THEN
  SI65_RIT_CALL_TAC "H_CHK54" [`word_add fp (word 10816):int64`;
    SI65_RIT_CT0; `word 261888:int32`; `word 0:int32`; `pc:num`] 53 THEN
  ARM_STEPS_TAC SI65_RIT_EXEC [54] THEN
  SI65_DECIDE_TAC `ok2:bool` THEN SI65_CASES_TAC `ok2:bool` THENL
   [ALL_TAC; SI65_RIT_FAIL_TAC `ok2:bool`];;

let SI65_RIT_LAST = prove
 (`!j. j < 6 ==> (j + 1 = 6 <=> ~(j + 1 < 6))`, ARITH_TAC);;

(*** The sum of the row and the back edge ***)

let SI65_RIT_PART3_TAC =
  SI65_RIT_CALL_TAC "H_RADD" [`fp:int64`; `word_add fp (word (3904 + 1024 * j)):int64`;
    SI65_RIT_R0; SI65_RIT_CT0; `j:num`; `6 + 416 * j`;
    `word_add fp (word (3904 + 1024 * j)):int64`;
    `word_add fp (word (3920 + 1024 * j)):int64`; `pc:num`] 55 THEN
  ARM_STEPS_TAC SI65_RIT_EXEC [56] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `j:num` SI65_RIT_LAST) (ASSUME `j < 6`)]) THEN
  SI65_CASES_TAC `j + 1 < 6` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES; ADD_ASSOC] THEN
      CONV_TAC WORD_RULE THEN NO_TAC) THEN
  SI65_END_TAC;;

let SI65_RIT = prove
 (SI65_RIT_STMT,
  MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n) (SI65_RIT_CALLEES ()) THEN
  CONCRETIZE_F_EVENTS_TAC SI65_RIT_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `ok1:bool`; `ok2:bool`; `sk:int64`;
                       `skb:num->byte`; `fp:int64`; `j:num`; `w:num->int32`;
                       `cphat:num->int32`; `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; fst SI65_RIT_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN SI65_ORIENT_TAC THEN
  SI65_FPB_TAC 11840 THEN FULL_INIT_TAC THEN
  SI65_RIT_PART1_TAC THEN SI65_RIT_PART2_TAC THEN SI65_RIT_PART3_TAC);;

(* ------------------------------------------------------------------------- *)
(* The loop over the rows of w0, for the first m rows, both of whose checks  *)
(* pass (RPRE), from the exit of the loop over z (loop36_exit1), where the   *)
(* code sets up row 0: row j of w holds w0_j - c s2_j + c t0_j afterwards    *)
(* (mld_sign_hint_x), the rows after the first m are unchanged.              *)
(* ------------------------------------------------------------------------- *)

let SI65_ORR_THM k c =
  let tm = parse_term(Printf.sprintf
    "aligned 32 (fp:int64)
     ==> word_or (word_add fp (word %d)) (word %d) = word_add fp (word %d)" k c (k+c)) in
  prove(tm, REWRITE_TAC[MLD_WRAP_ALIGNED_16_32] THEN
            W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let SI65_ALIGNED16_32 = prove
 (`!x:int64. aligned 32 x ==> aligned 16 x`,
  REWRITE_TAC[MLD_WRAP_ALIGNED_16_32] THEN
  GEN_TAC THEN W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let SI65_RPRE_HX = list_mk_comb(`mld_sign_hint_x 6 mld_poly_decompose_lo_32`,
  [`w:num->int32`; SI65_S2H; SI65_T0H; `cphat:num->int32`]);;

let SI65_RPRE_STMT = parse_term(
 "exists f_events.
    forall e m sk skb fp w cphat pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 32 fp /\\ val fp + 12960 < 2 EXP 63 /\\ m <= 6 /\\
      (!j. j < m ==> mld_poly_chknorm (" ^ string_of_term SI65_RIT_R0 ^ ") (word 261692) =
                     word 0 /\\
                     mld_poly_chknorm (" ^ string_of_term SI65_RIT_CT0 ^ ") (word 261888) =
                     word 0) /\\
      ALL (nonoverlapping (word_sub fp (word 1472),14432))
          [(sk,4032); (word pc,libmldsa_size)]
      ==> ensures arm
           (\\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read PC s = word (pc + mldsa65_signature_internal_loop36_exit1) /\\\n" ^
  SI65_RIT_PRE ^ " /\\
                (!i. i < 1536 ==> read (memory :> bytes32 (word_add fp (word (3904 + 4 * i)))) s =
                                  mld_polyvec_map mld_poly_decompose_lo_32 w i) /\\
                read events s = e)
           (\\s. read PC s =
                (if m < 6 then word (pc + mldsa65_signature_internal_loop45)
                 else word (pc + mldsa65_signature_internal_loop45_exit1)) /\\
                read SP s = fp /\\ " ^ SI65_RIT_ROW "m" ^ SI65_RIT_CONST ^
 "              (0 < m ==> read X25 s = word_add fp (word 3904)) /\\
                (!i. i < 256 * m ==> read (memory :> bytes32 (word_add fp (word (3904 + 4 * i)))) s =
                                     " ^ string_of_term SI65_RPRE_HX ^ " i) /\\
                (!i. 256 * m <= i /\\ i < 1536
                     ==> read (memory :> bytes32 (word_add fp (word (3904 + 4 * i)))) s =
                         mld_polyvec_map mld_poly_decompose_lo_32 w i) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events m sk fp pc /\\
                   memaccess_inbounds e2
                    [sk,4032; word_sub fp (word 1472),14432;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa65_signature_internal_consts),336]
                    [word_sub fp (word 1472),14432]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [X18; X21; X22; X23; X25; X27; X30] ,,
            MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
            MAYCHANGE [memory :> bytes(word_sub fp (word 208),208);
                       memory :> bytes(word_add fp (word 416),8);
                       memory :> bytes(word_add fp (word 3904),6144);
                       memory :> bytes(word_add fp (word 10816),1024)])");;

let SI65_RPRE_EXEC = SI65_EXEC_RANGE "loop36_exit1" "loop45_exit1";;

let SI65_RPRE_INV = parse_term(
 "\\i s. " ^ SI65_RIT_ROW "i" ^ SI65_RIT_CONST ^ SI65_RIT_PRE ^ " /\\
        (0 < i ==> read X25 s = word_add fp (word 3904)) /\\
        (!k. k < 256 * i ==> read (memory :> bytes32 (word_add fp (word (3904 + 4 * k)))) s =
                             " ^ string_of_term SI65_RPRE_HX ^ " k) /\\
        (!k. 256 * i <= k /\\ k < 1536
             ==> read (memory :> bytes32 (word_add fp (word (3904 + 4 * k)))) s =
                 mld_polyvec_map mld_poly_decompose_lo_32 w k)");;

let SI65_RPRE_PC = prove
 (`!i m a b. i < m /\ m <= 6
             ==> (if i + 1 < 6 then word a else word b):int64 =
                 word (if i + 1 < m then a else if m < 6 then a else b)`,
  REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMPLE_ARITH_TAC);;

(*** The setup of row 0 (13 instructions, the ADRPs at steps 10 to 13) ***)

let SI65_RPRE_SETUP_TAC =
  ARM_STEPS_TAC SI65_RPRE_EXEC (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SI65_ORR_THM 3904 16) (ASSUME `aligned 32 (fp:int64)`)]) THEN
  SI65_ADRP_STEPS_TAC SI65_RPRE_EXEC (10--13);;

let SI65_RPRE_ALLOWED = [`sk:int64`; `fp:int64`; `pc:num`; `i:num`];;

let SI65_LOOP_MEMACCESS_TAC =
  SIGN_BETA_ALL_TAC THEN SIGN_SPLIT_MEMACCESS_ASM_TAC THEN SI65_FB_NORM_TAC 1472 THEN
  REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

let SI65_LOOP_END_TAC =
  SIGN_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [SIGN_LOOP_UNIFY_TAC; SI65_LOOP_MEMACCESS_TAC];;

let SI65_RPRE_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `i < 6` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    can (term_match [] `!j. j < m ==> P j /\ Q j`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FULL_INIT_TAC THEN
  MP_TAC(SPECL [`fp:int64`; `3904`; `1536`; `mld_poly_decompose_lo_32`;
                `w:num->int32`; `i:num`; `s0:armstate`] SIGN_ROW_SLICE) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [`i:num`; `s0:armstate`]
             `!k. 256 * i <= k /\ k < 1536
                  ==> read (memory :> bytes32 (word_add fp (word (3904 + 4 * k)))) s0 = Q k`)
           (concl th)
    then REWRITE_TAC[th] else NO_TAC) THEN
  ANTS_TAC THENL [UNDISCH_TAC `i < 6` THEN ARITH_TAC; STRIP_TAC] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc SI65_RPRE_EXEC "H_RIT"
   [`T`; `T`; `sk:int64`; `skb:num->byte`; `fp:int64`; `i:num`; `w:num->int32`;
    `cphat:num->int32`; `pc:num`] SI65_RPRE_ALLOWED 1 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SI65_RPRE_PC
                               (CONJ (ASSUME `i < m`) (ASSUME `m <= 6`))]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ARITH_RULE `0 < i + 1`] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SIGN_ROW_JOIN THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
  (SI65_MAYCHANGE_TAC ORELSE SI65_LOOP_END_TAC);;

let SI65_CLOSED_END_TAC =
  W(fun (asl,w) ->
    let _,bod = dest_exists w in
    match conjuncts bod with
      [_; eq; _] -> EXISTS_TAC (rhs eq)
    | _ -> failwith "SI65_CLOSED_END_TAC") THEN
  SIGN_BETA_ALL_TAC THEN REWRITE_TAC[ENUMERATEL; APPEND; APPEND_NIL] THEN
  REPEAT CONJ_TAC THEN
  TRY(ASM_REWRITE_TAC[APPEND; APPEND_NIL; GSYM APPEND_ASSOC] THEN NO_TAC) THEN
  SI65_FB_NORM_TAC 1472 THEN REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

let SI65_RPRE = prove
 (SI65_RPRE_STMT,
  SI65_ASSUME_CALLEE_TAILED_TAC SI65_RIT "H_RIT" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(m:num) (sk:int64) (fp:int64) (pc:num).
     APPEND (f_ev_back m sk fp pc)
      (APPEND (ENUMERATEL m (\i. f_ev_rit sk fp pc i)) (f_ev_front sk fp pc))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `m:num`; `sk:int64`; `skb:num->byte`;
    `fp:int64`; `w:num->int32`; `cphat:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst SI65_RPRE_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SI65_ALIGNED16_32) THEN
  ASM_CASES_TAC `0 < m` THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `m:num`
     `pc + mldsa65_signature_internal_loop45`
     `if m < 6 then pc + mldsa65_signature_internal_loop45
      else pc + mldsa65_signature_internal_loop45_exit1`
     SI65_RPRE_INV THEN
    REPEAT CONJ_TAC THENL
     [SIMPLE_ARITH_TAC;
      REWRITE_TAC[CONJUNCT1 LT; MULT_CLAUSES; ADD_CLAUSES; LE_0] THEN
      FULL_INIT_TAC THEN SI65_RPRE_SETUP_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN SI65_END_TAC;
      SI65_RPRE_BODY_TAC;
      REWRITE_TAC[] THEN FULL_INIT_TAC THEN SIGN_PC_COND_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      SIGN_BETA_ALL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC];
    SUBGOAL_THEN `m = 0` SUBST_ALL_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN SI65_RPRE_SETUP_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ARITH; MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    REWRITE_TAC[ENUMERATEL; APPEND; APPEND_NIL] THEN SI65_CLOSED_END_TAC]);;

(* ------------------------------------------------------------------------- *)
(* s1 in the NTT domain and y, with y sampled from rho'' (RHO, at fp + 1792) *)
(* with the nonce 5 att + i.                                                 *)
(* ------------------------------------------------------------------------- *)

let SI65_S1U =
 `mld_polyvec_unpack 128 mld_polyeta_unpack_4 (\j. (skb:num->byte)(128 + j))`;;
let SI65_S1H = mk_comb(`mld_polyvec_map mld_poly_ntt`,SI65_S1U);;
let SI65_YK = `mld_sign_y mld_poly_uniform_gamma1_19 RHO (5 * att)`;;
let SI65_ZI = list_mk_comb(`mld_sign_z`, [SI65_S1H; `cphat:num->int32`; SI65_YK; `i:num`]);;

(* ------------------------------------------------------------------------- *)
(* One iteration of the loop over z (ZIT), from loop36 with i in x25: s1_i  *)
(* unpacked into fp + 1856 and transformed, its product with the challenge   *)
(* and the inverse NTT, y_i sampled again (the inlined poly_uniform_gamma1   *)
(* with the nonce 5 att + i), the sum, the reduction and the norm check of   *)
(* z_i; if it passes (ok), z_i packed into the signature at sig + 48 + 640 i *)
(* and back to loop36 or, after the last, to loop36_exit1; else to           *)
(* loop36_exit2.                                                             *)
(* ------------------------------------------------------------------------- *)

let SI65_ZIT_PRE =
 "read SP s = fp /\\
  read X20 s = word_add fp (word 10816) /\\ read X21 s = word_add fp (word 11936) /\\
  read X22 s = word_add fp (word 1856) /\\
  read X26 s = word 18446744073701171199 /\\ read X19 s = word 252236767799803904 /\\
  read X28 s = word_add fp (word 10824) /\\
  read (memory :> bytes64 (word_add fp (word 320))) s = word_add fp (word 2888) /\\
  read (memory :> bytes64 (word_add fp (word 352))) s = word_add fp (word 12265) /\\
  read (memory :> bytes64 (word_add fp (word 360))) s = word_add fp (word 2880) /\\
  read (memory :> bytes64 (word_add fp (word 512))) s = word_add sk (word 128) /\\
  read (memory :> bytes64 (word_add fp (word 11840))) s = word_add fp (word 1792) /\\
  read (memory :> bytes16 (word_add fp (word 11848))) s = word (5 * att) /\\
  read (memory :> bytes128 (word_add fp (word 368))) s =
  word 339618401959998730991157055895298383871 /\\
  read (memory :> bytes (word_add fp (word 1792),64)) s = RHO /\\
  (!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (2880 + 4 * i)))) s =
                   cphat i) /\\
  (!i. i < 4032 ==> read (memory :> bytes8 (word_add sk (word i))) s = skb i) /\\
  read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
  read (memory :> bytes(ea,el)) s = ev";;

let SI65_ZIT_STMT = parse_term(
 "!mf mc ea el ev.
   memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
   ==> exists f_events.
        forall e ok sig sk skb fp i cphat RHO att pc.
         aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
         aligned 32 fp /\\ val fp + 12960 < 2 EXP 63 /\\ i < 5 /\\ att < 13106 /\\
         (ok <=> mld_poly_chknorm (" ^ string_of_term SI65_ZI ^ ") (word 524092) = word 0) /\\
         nonoverlapping (sig,3309) (word_sub fp (word 1472),14432) /\\
         ALL (nonoverlapping (word_sub fp (word 1472),14432))
             [(sk,4032); (word pc,libmldsa_size); (word(pc + got_memset),8);
              (word(pc + got_memcpy),8); (ea,el)] /\\
         ALL (nonoverlapping (sig,3309))
             [(sk,4032); (word pc,libmldsa_size); (word(pc + got_memset),8);
              (word(pc + got_memcpy),8); (ea,el)]
         ==> ensures arm
              (\\s. aligned_bytes_loaded s (word pc)
                     mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                   read PC s = word (pc + mldsa65_signature_internal_loop36) /\\
                   read X25 s = word i /\\ read X12 s = word (128 * i) /\\
                   read X14 s = word 4 /\\
                   read X27 s = word_add sig (word (640 * i)) /\\\n" ^ SI65_ZIT_PRE ^ " /\\
                   read events s = e)
              (\\s. read PC s =
                   (if ok then (if i + 1 < 5 then word (pc + mldsa65_signature_internal_loop36)
                                else word (pc + mldsa65_signature_internal_loop36_exit1))
                    else word (pc + mldsa65_signature_internal_loop36_exit2)) /\\
                   read SP s = fp /\\
                   read X21 s = word_add fp (word 11936) /\\
                   read X22 s = word_add fp (word 1856) /\\
                   read X24 s = word 523777 /\\
                   (ok ==> read X25 s = word (i + 1) /\\ read X12 s = word (128 * (i + 1)) /\\
                           read X14 s = word 4 /\\
                           read X27 s = word_add sig (word (640 * (i + 1))) /\\
                           (!t. t < 640
                                ==> read (memory :> bytes8 (word_add sig (word ((48 + 640 * i) + t)))) s =
                                    mld_polyz_pack_19 (" ^ string_of_term SI65_ZI ^ ") t)) /\\
                   (exists e2.
                      read events s = APPEND e2 e /\\
                      e2 = f_events ok sig sk fp i mf mc pc /\\
                      memaccess_inbounds e2
                       [sig,3309; sk,4032; word_sub fp (word 1472),14432;
                        word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                        word(pc + rodata_mld_KeccakF_RoundConstants),192;
                        word(pc + rodata_mld_zetas),1024;
                        word(pc + mldsa65_signature_internal_consts),336]
                       [sig,3309; word_sub fp (word 1472),14432]))
              (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [X18; X21; X22; X23; X24; X25; X27; X30] ,,
               MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
               MAYCHANGE [memory :> bytes(word_sub fp (word 240),240);
                          memory :> bytes(word_add fp (word 384),8);
                          memory :> bytes(word_add fp (word 416),8);
                          memory :> bytes(word_add fp (word 1856),1024);
                          memory :> bytes(word_add fp (word 10816),1024);
                          memory :> bytes(word_add fp (word 11936),1000);
                          memory :> bytes(word_add sig (word (48 + 640 * i)),640)])");;

let SI65_ZIT_EXEC = SI65_EXEC_RANGE "loop36" "loop36_exit1";;

let SI65_ZIT_TEMPLATE =
 `\(ok:bool) (sig:int64) (sk:int64) (fp:int64) (i:num) (mf:int64) (mc:int64) (pc:num).
   if ok then (if i + 1 < 5 then f_ev_mid sig sk fp i mf mc pc
               else f_ev_last sig sk fp i mf mc pc)
   else f_ev_f sig sk fp i mf mc pc :(uarch_event)list`;;

let SI65_ZIT_ALLOWED = [`ok:bool`; `sig:int64`; `sk:int64`; `fp:int64`; `i:num`;
                        `mf:int64`; `mc:int64`; `pc:num`];;

let SI65_ZIT_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc SI65_ZIT_EXEC
    name ilist SI65_ZIT_ALLOWED n;;

let SI65_SLICE_GEN_TAC base idx lim aoff voff n st =
  let t = vsubst [st,`s:armstate`] (parse_term(Printf.sprintf
   "!k. k < %d ==> read (memory :> bytes8 (word_add %s (word (%s + k)))) s =
                   (skb:num->byte) (%s + k)" n base aoff voff)) in
  let ilt = parse_term(Printf.sprintf "%s < %d" idx lim) in
  SUBGOAL_THEN t ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[GSYM ADD_ASSOC] THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (term_match []
       `!i. i < 4032 ==> read (memory :> bytes8 (word_add sk (word i))) s = skb i`)
       (concl th))) THEN
    MAP_EVERY UNDISCH_TAC [ilt; mk_binop `(<):num->num->bool` `k:num` (mk_small_numeral n)] THEN
    ARITH_TAC;
    ALL_TAC];;

(*** The frame of the inlined poly_uniform_gamma1 (fr = fp - 240) in the    ***)
(*** forms of fp                                                            ***)

let SI65_FR_EQS ks tks =
  map (fun k ->
    let tm = if k = 240 then `word_add (word_sub fp (word 240)) (word 240):int64 = fp`
      else parse_term(Printf.sprintf
        "word_add (word_sub fp (word 240)) (word %d):int64 = word_add fp (word %d)"
        k (k - 240)) in
    WORD_RULE tm) ks @
  map (fun k ->
    prove(parse_term(Printf.sprintf
      "!t. word_add (word_sub fp (word 240)) (word (%d + t)):int64 =
           word_add fp (word (%d + t))" k (k - 240)),
     GEN_TAC THEN REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE)) tks;;

let SI65_FR_Z = SI65_FR_EQS [240; 12080; 12088; 12176; 592; 12505; 11056; 12400; 12496]
                            [11056; 12496];;

let SI65_ZTEST5 = prove
 (`!i. i < 5
       ==> (val (word_sub (word (i + 1)) (word 5):int64) = 0 <=> ~(i + 1 < 5)) /\
           (val (word_add (word (i + 1)) (word 18446744073709551611):int64) = 0 <=>
            ~(i + 1 < 5)) /\
           (val (word_add (word i) (word 18446744073709551612):int64) = 0 <=>
            ~(i + 1 < 5))`,
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV)) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let SI65_ZIT_POLY v = mk_comb(mk_comb(`mld_poly_of`,v),`i:num`);;
let SI65_ZIT_PW = list_mk_comb(`mld_poly_pointwise_montgomery`,
  [SI65_ZIT_POLY SI65_S1H; `cphat:num->int32`]);;
let SI65_ZIT_CS1 = mk_comb(`mld_poly_invntt_tomont`,SI65_ZIT_PW);;
let SI65_ZIT_Y = SI65_ZIT_POLY SI65_YK;;

let SI65_ZIT = prove
 (SI65_ZIT_STMT,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP SI65_G1_Z th) "H_G1" THEN
    MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
     [SI65_ETA_Z,"H_ETA";
      MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_NTT";
      MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_INV";
      SI65_LK SI65_PWM "loop39","H_PWM39"; SI65_ZADD,"H_ZADD";
      SI65_LK SI65_RED "loop42","H_RED42"; SI65_LK SI65_CHK "loop43","H_CHK43";
      SI65_ZPACK,"H_ZPACK"]) THEN
  CONCRETIZE_F_EVENTS_TAC SI65_ZIT_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `ok:bool`; `sig:int64`; `sk:int64`;
    `skb:num->byte`; `fp:int64`; `i:num`; `cphat:num->int32`; `RHO:num`; `att:num`;
    `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; fst SI65_ZIT_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SI65_ALIGNED16_32) THEN
  FIRST_X_ASSUM(fun th -> if is_iff(concl th) && lhs(concl th) = `ok:bool`
                          then ASSUME_TAC(GSYM th) else NO_TAC) THEN
  SI65_FPB_TAC 2880 THEN FULL_INIT_TAC THEN
  (*** s1_i, its NTT, the product and the inverse NTT ***)
  SI65_SLICE_GEN_TAC "sk" "i" 5 "128 + 128 * i" "128 + 128 * i" 128 `s0:armstate` THEN
  SUBGOAL_THEN `i < 8` ASSUME_TAC THENL [UNDISCH_TAC `i < 5` THEN ARITH_TAC; ALL_TAC] THEN
  SI65_ZIT_CALL_TAC "H_ETA" [`fp:int64`; `word_add sk (word 128):int64`; `i:num`;
    `\k. (skb:num->byte) (128 + 128 * i + k)`; `pc:num`] 1 THEN
  MLD_LAZY_REPOLY_TAC `mld_polyeta_unpack_4 (\k. (skb:num->byte) (128 + 128 * i + k))`
    (SI65_ZIT_POLY SI65_S1U) [mld_polyvec_unpack; MLD_POLY_OF_POLYVEC] THEN
  ARM_STEPS_TAC SI65_ZIT_EXEC (2--3) THEN
  SI65_ZIT_CALL_TAC "H_NTT" [`read X0 s`; SI65_ZIT_POLY SI65_S1U; `pc:num`;
                              `read SP s`; `read X30 s`] 4 THEN
  MLD_LAZY_REPOLY_TAC (mk_comb(`mld_poly_ntt`,SI65_ZIT_POLY SI65_S1U))
    (SI65_ZIT_POLY SI65_S1H) [MLD_POLY_OF_POLYVEC_MAP] THEN
  ARM_STEPS_TAC SI65_ZIT_EXEC (5--6) THEN
  SI65_ZIT_CALL_TAC "H_PWM39" [`word_add fp (word 1856):int64`;
    `word_add fp (word 2880):int64`; SI65_ZIT_POLY SI65_S1H; `cphat:num->int32`;
    `pc:num`] 7 THEN
  ARM_STEPS_TAC SI65_ZIT_EXEC (8--9) THEN
  SI65_ZIT_CALL_TAC "H_INV" [`read X0 s`; SI65_ZIT_PW; `pc:num`; `read SP s`;
                              `read X30 s`] 10 THEN
  (*** y_i ***)
  ARM_STEPS_TAC SI65_ZIT_EXEC (11--16) THEN
  MAP_EVERY ASSUME_TAC SI65_FR_Z THEN
  SI65_ZIT_CALL_TAC "H_G1" [`word_add fp (word 1792):int64`; `RHO:num`; `5 * att`;
    `i:num`; `word_sub fp (word 240):int64`; `pc:num`] 17 THEN
  RULE_ASSUM_TAC(REWRITE_RULE SI65_FR_Z) THEN
  MLD_LAZY_REPOLY_TAC `mld_poly_uniform_gamma1_19 RHO (word (5 * att + i))` SI65_ZIT_Y
    [mld_sign_y; MLD_POLY_OF_POLYVEC] THEN
  (*** z_i = c s1_i + y_i, reduced, and its check ***)
  SI65_ZIT_CALL_TAC "H_ZADD" [`fp:int64`; SI65_ZIT_CS1; SI65_ZIT_Y; `pc:num`] 18 THEN
  SI65_ZIT_CALL_TAC "H_RED42" [`word_add fp (word 1856):int64`;
    list_mk_comb(`mld_poly_add`,[SI65_ZIT_CS1; SI65_ZIT_Y]); `pc:num`] 19 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_z]) THEN
  ARM_STEPS_TAC SI65_ZIT_EXEC (20--22) THEN
  SI65_ADRP_STEPS_TAC SI65_ZIT_EXEC (23--36) THEN
  SI65_REG_FORM_TAC "X24" 36
    `word_zx (word_sub (word_sub (word 524092:int32) (word 1)) (word 314)):int64` THEN
  SI65_REG_FORM_TAC "X8" 36 `word_zx (word 0:int32):int64` THEN
  SI65_ZIT_CALL_TAC "H_CHK43" [`word_add fp (word 1856):int64`; SI65_ZI;
    `word 524092:int32`; `word 0:int32`; `pc:num`] 37 THEN
  ARM_STEPS_TAC SI65_ZIT_EXEC (38--39) THEN
  SI65_DECIDE_TAC `ok:bool` THEN SI65_CASES_TAC `ok:bool` THENL
   [ALL_TAC;
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV WORD_RED_CONV)) THEN SI65_RIT_FAIL_TAC `ok:bool`] THEN
  (*** the packing of z_i and the back edge ***)
  ARM_STEPS_TAC SI65_ZIT_EXEC (40--41) THEN
  SI65_ADRP_STEPS_TAC SI65_ZIT_EXEC [42] THEN
  SI65_ZIT_CALL_TAC "H_ZPACK" [`fp:int64`; `word_add sig (word (640 * i)):int64`;
    SI65_ZI; `pc:num`] 43 THEN
  ARM_STEPS_TAC SI65_ZIT_EXEC (44--54) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `i:num` SI65_ZTEST5) (ASSUME `i < 5`)]) THEN
  SI65_CASES_TAC `i + 1 < 5` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(CONV_TAC WORD_REDUCE_CONV THEN NO_TAC) THEN
  TRY(REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES; ADD_ASSOC] THEN
      CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(X_GEN_TAC `t:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:num`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `(48 + 640 * i) + t = 640 * i + 48 + t`] THEN NO_TAC) THEN
  SI65_END_TAC);;

(* ------------------------------------------------------------------------- *)
(* The loop over z, for the first m polynomials, each of which passes the    *)
(* norm check (ZPRE), from after the NTT of the challenge, where the code    *)
(* sets up i = 0: the first 640 m bytes of z packed are in the signature at  *)
(* sig + 48.                                                                 *)
(* ------------------------------------------------------------------------- *)

let SI65_ZPRE_Z = list_mk_comb(`mld_sign_z`, [SI65_S1H; `cphat:num->int32`; SI65_YK]);;
let SI65_ZPRE_ZI = mk_comb(SI65_ZPRE_Z,`i:num`);;

let SI65_ZPRE_STMT = parse_term(
 "!mf mc ea el ev.
   memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
   ==> exists f_events.
        forall e m sig sk skb fp cphat RHO att pc.
         aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
         aligned 32 fp /\\ val fp + 12960 < 2 EXP 63 /\\ m <= 5 /\\ att < 13106 /\\
         (!i. i < m ==> mld_poly_chknorm (" ^ string_of_term SI65_ZPRE_ZI ^ ") (word 524092) =
                        word 0) /\\
         nonoverlapping (sig,3309) (word_sub fp (word 1472),14432) /\\
         ALL (nonoverlapping (word_sub fp (word 1472),14432))
             [(sk,4032); (word pc,libmldsa_size); (word(pc + got_memset),8);
              (word(pc + got_memcpy),8); (ea,el)] /\\
         ALL (nonoverlapping (sig,3309))
             [(sk,4032); (word pc,libmldsa_size); (word(pc + got_memset),8);
              (word(pc + got_memcpy),8); (ea,el)]
         ==> ensures arm
              (\\s. aligned_bytes_loaded s (word pc)
                     mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                   read PC s = word (pc + mldsa65_signature_internal_after_mldsa_poly_ntt_2) /\\
                   read (memory :> bytes64 (word_add fp (word 64))) s = sig /\\\n" ^
  SI65_ZIT_PRE ^ " /\\
                   read events s = e)
              (\\s. read PC s =
                   (if m < 5 then word (pc + mldsa65_signature_internal_loop36)
                    else word (pc + mldsa65_signature_internal_loop36_exit1)) /\\
                   read SP s = fp /\\
                   read X25 s = word m /\\ read X12 s = word (128 * m) /\\
                   read X14 s = word 4 /\\
                   read X27 s = word_add sig (word (640 * m)) /\\
                   read X21 s = word_add fp (word 11936) /\\
                   read X22 s = word_add fp (word 1856) /\\
                   (0 < m ==> read X24 s = word 523777) /\\
                   (!t. t < 640 * m
                        ==> read (memory :> bytes8 (word_add sig (word (48 + t)))) s =
                            mld_polyvec_pack 640 mld_polyz_pack_19
                             (mld_polyvec (" ^ string_of_term SI65_ZPRE_Z ^ ")) t) /\\
                   (exists e2.
                      read events s = APPEND e2 e /\\
                      e2 = f_events m sig sk fp mf mc pc /\\
                      memaccess_inbounds e2
                       [sig,3309; sk,4032; word_sub fp (word 1472),14432;
                        word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                        word(pc + rodata_mld_KeccakF_RoundConstants),192;
                        word(pc + rodata_mld_zetas),1024;
                        word(pc + mldsa65_signature_internal_consts),336]
                       [sig,3309; word_sub fp (word 1472),14432]))
              (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [X18; X21; X22; X23; X24; X25; X27; X30] ,,
               MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
               MAYCHANGE [memory :> bytes(word_sub fp (word 240),240);
                          memory :> bytes(word_add fp (word 384),8);
                          memory :> bytes(word_add fp (word 416),8);
                          memory :> bytes(word_add fp (word 1856),1024);
                          memory :> bytes(word_add fp (word 10816),1024);
                          memory :> bytes(word_add fp (word 11936),1000);
                          memory :> bytes(word_add sig (word 48),3200)])");;

let SI65_ZPRE_EXEC = SI65_EXEC_RANGE "after_mldsa_poly_ntt_2" "loop36_exit1";;

let SI65_ZPRE_INV = parse_term(
 "\\i s. read X25 s = word i /\\ read X12 s = word (128 * i) /\\
        read X14 s = word 4 /\\
        read X27 s = word_add sig (word (640 * i)) /\\
        read (memory :> bytes64 (word_add fp (word 64))) s = sig /\\
        (0 < i ==> read X24 s = word 523777) /\\\n" ^ SI65_ZIT_PRE ^ " /\\
        (!t. t < 640 * i
             ==> read (memory :> bytes8 (word_add sig (word (48 + t)))) s =
                 mld_polyvec_pack 640 mld_polyz_pack_19
                  (mld_polyvec (" ^ string_of_term SI65_ZPRE_Z ^ ")) t)");;

let SI65_ZPRE_ALLOWED = [`sig:int64`; `sk:int64`; `fp:int64`; `mf:int64`; `mc:int64`;
                         `pc:num`; `i:num`];;

let SI65_ZPRE_PC = prove
 (`!i m a b. i < m /\ m <= 5
             ==> (if i + 1 < 5 then word a else word b):int64 =
                 word (if i + 1 < m then a else if m < 5 then a else b)`,
  REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMPLE_ARITH_TAC);;

let SI65_ZPRE_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `i < 5` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o C MP (ASSUME `i < m`) o SPEC `i:num` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `mld_poly_chknorm`)) (concl th))) THEN
  FULL_INIT_TAC THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc SI65_ZPRE_EXEC "H_ZIT"
   [`T`; `sig:int64`; `sk:int64`; `skb:num->byte`; `fp:int64`; `i:num`;
    `cphat:num->int32`; `RHO:num`; `att:num`; `pc:num`] SI65_ZPRE_ALLOWED 1 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SI65_ZPRE_PC
                               (CONJ (ASSUME `i < m`) (ASSUME `m <= 5`))]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ARITH_RULE `0 < i + 1`] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC(ISPECL [`mld_polyz_pack_19`; `640`] SIGN_PACK_JOIN) THEN
      ASM_REWRITE_TAC[SIGN_POLYZ_PACK_19_LOCAL] THEN
      REWRITE_TAC[ADD_ASSOC] THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
  (SI65_MAYCHANGE_TAC ORELSE SI65_LOOP_END_TAC);;

let SI65_ZPRE_SETUP_TAC = ARM_STEPS_TAC SI65_ZPRE_EXEC (1--4);;

let SI65_ZPRE = prove
 (SI65_ZPRE_STMT,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    SI65_ASSUME_CALLEE_TAILED_TAC (MATCH_MP SI65_ZIT th) "H_ZIT") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(m:num) (sig:int64) (sk:int64) (fp:int64) (mf:int64) (mc:int64) (pc:num).
     APPEND (f_ev_back m sig sk fp mf mc pc)
      (APPEND (ENUMERATEL m (\i. f_ev_zit sig sk fp mf mc pc i))
              (f_ev_front sig sk fp mf mc pc))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `m:num`; `sig:int64`; `sk:int64`;
    `skb:num->byte`; `fp:int64`; `cphat:num->int32`; `RHO:num`; `att:num`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst SI65_ZPRE_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SI65_ALIGNED16_32) THEN
  ASM_CASES_TAC `0 < m` THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `m:num`
     `pc + mldsa65_signature_internal_loop36`
     `if m < 5 then pc + mldsa65_signature_internal_loop36
      else pc + mldsa65_signature_internal_loop36_exit1`
     SI65_ZPRE_INV THEN
    REPEAT CONJ_TAC THENL
     [SIMPLE_ARITH_TAC;
      REWRITE_TAC[CONJUNCT1 LT; MULT_CLAUSES; ADD_CLAUSES; LE_0] THEN
      FULL_INIT_TAC THEN SI65_ZPRE_SETUP_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN SI65_END_TAC;
      SI65_ZPRE_BODY_TAC;
      REWRITE_TAC[] THEN FULL_INIT_TAC THEN SIGN_PC_COND_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      SIGN_BETA_ALL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC];
    SUBGOAL_THEN `m = 0` SUBST_ALL_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN SI65_ZPRE_SETUP_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ARITH; MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    REWRITE_TAC[ENUMERATEL; APPEND; APPEND_NIL] THEN SI65_CLOSED_END_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The end of the start of an attempt (HPOST), from the exit of the loop     *)
(* over the columns of y (loop3_exit), where row k of w holds the sums       *)
(* mld_lazy_acc rho k y^ 4: the zeroing of the seed of the matrix, the       *)
(* reduction, the inverse NTT and caddq of each row (mld_sign_w, by          *)
(* MLD_LAZY_SIGN_W), the decomposition of each row with w0 in place and w1   *)
(* packed at fp + 10048 + 128 k, c~ = SHAKE256(mu || w1) at fp + 11872 by    *)
(* mld_H65, the challenge at fp + 2880 and its NTT.                          *)
(* ------------------------------------------------------------------------- *)

let SI65_YH = `mld_polyvec_map mld_poly_ntt (mld_sign_y mld_poly_uniform_gamma1_19 RHO (5 * att))`;;
let SI65_W = `mld_sign_w 5 (mld_polyvec_matrix_expand 5 rho)
               (mld_sign_y mld_poly_uniform_gamma1_19 RHO (5 * att))`;;
let SI65_W1 = mk_comb(`mld_sign_w1 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128`,SI65_W);;
let SI65_CT = mk_comb(`mld_sign_ctilde 6 128 MU`,SI65_W1);;
let SI65_CTN = mk_comb(`num_of_bytelist`,list_mk_comb(`list_of_seq:(num->byte)->num->byte list`,
                                                     [SI65_CT; `48`]));;

let SI65_ACC_ROWS = String.concat "" (map (fun k -> Printf.sprintf
  "(!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (%d + 4 * i)))) s =
                   mld_lazy_acc rho %d (%s) 4 i) /\\\n" (3904 + 1024 * k) k
  (string_of_term SI65_YH)) (0--5));;

let SI65_HPOST_STMT = parse_term(
 "!mf mc ea el ev.
   memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
   ==> exists f_events.
        forall e fp rho RHO MU att C guard pc.
         aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
         aligned 32 fp /\\ att < 13106 /\\ mld_matrix_terminates 6 5 rho /\\
         " ^ string_of_term SI65_CTN ^ " = C /\\
         mld_poly_challenge_terminates 49 48 C /\\
         ALL (nonoverlapping (word_sub fp (word 1472),14432))
             [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8); (guard,8);
              (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
         ==> ensures arm
              (\\s. aligned_bytes_loaded s (word pc)
                     mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                   read PC s = word (pc + mldsa65_signature_internal_loop3_exit) /\\
                   read SP s = fp /\\
                   read X24 s = word_add fp (word 3904) /\\ read X20 s = word_add fp (word 10816) /\\
                   read (memory :> bytes128 (word_add fp (word 368))) s =
                   word 339618401959998730991157055895298383871 /\\\n" ^
  SI65_SLOT_FACTS [344,9024] ^
  SI65_ACC_ROWS ^
 "                 read (memory :> bytes (word_add fp (word 1728),64)) s = MU /\\
                   read (memory :> bytes64(word(pc + got_stack_chk_guard))) s = guard /\\
                   read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                   read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                   read (memory :> bytes(ea,el)) s = ev /\\
                   read events s = e)
              (\\s. read PC s = word (pc + mldsa65_signature_internal_after_mldsa_poly_ntt_2) /\\
                   read SP s = fp /\\
                   read X20 s = word_add fp (word 10816) /\\
                   read X22 s = word_add fp (word 1856) /\\
                   (!i. i < 1536 ==> read (memory :> bytes32 (word_add fp (word (3904 + 4 * i)))) s =
                                     mld_polyvec_map mld_poly_decompose_lo_32 (" ^
                                       string_of_term SI65_W ^ ") i) /\\
                   (!j. j < 768 ==> read (memory :> bytes8 (word_add fp (word (10048 + j)))) s =
                                    " ^ string_of_term SI65_W1 ^ " j) /\\
                   read (memory :> bytes (word_add fp (word 11872),48)) s = C /\\
                   (!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (2880 + 4 * i)))) s =
                                    mld_sign_cphat 49 48 (" ^ string_of_term SI65_CT ^ ") i) /\\
                   (exists e2.
                      read events s = APPEND e2 e /\\
                      e2 = f_events fp guard mf mc pc C /\\
                      memaccess_inbounds e2
                       [word_sub fp (word 1472),14432;
                        word(pc + got_stack_chk_guard),8; guard,8;
                        word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                        word(pc + rodata_mld_KeccakF_RoundConstants),192;
                        word(pc + rodata_mld_zetas),1024;
                        word(pc + mldsa65_signature_internal_consts),336]
                       [word_sub fp (word 1472),14432]))
              (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [X18; X22; X23; X30] ,,
               MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
               MAYCHANGE [memory :> bytes(word_sub fp (word 768),768);
                          memory :> bytes(word_add fp (word 80),240);
                          memory :> bytes(word_add fp (word 384),16);
                          memory :> bytes(word_add fp (word 416),16);
                          memory :> bytes(word_add fp (word 2880),1024);
                          memory :> bytes(word_add fp (word 3904),6144);
                          memory :> bytes(word_add fp (word 10048),768);
                          memory :> bytes(word_add fp (word 10816),1024);
                          memory :> bytes(word_add fp (word 11872),48);
                          memory :> bytes(word_add fp (word 12160),64)])");;

let SI65_HPOST_EXEC = SI65_EXEC_RANGE "loop3_exit" "after_mldsa_poly_ntt_2";;

let SI65_HV = mk_comb(`mld_polyvec`,mk_abs(`i:num`,
  list_mk_comb(`mld_lazy_acc`,[`rho:num`; `i:num`; SI65_YH; `4`])));;
let SI65_HV1 = mk_comb(`mld_polyvec_map mld_poly_reduce`,SI65_HV);;
let SI65_HV2 = mk_comb(`mld_polyvec_map mld_poly_invntt_tomont`,SI65_HV1);;
let SI65_YVL = `mld_polyvec_matrix_yvec_lazy 5 rho
                 (mld_sign_y mld_poly_uniform_gamma1_19 RHO (5 * att))`;;
let SI65_HV3 = mk_comb(`mld_polyvec_map mld_poly_caddq`,SI65_YVL);;

let SI65_YVL_EQ = prove
 (mk_eq(SI65_YVL,SI65_HV2),
  REWRITE_TAC[mld_polyvec_matrix_yvec_lazy] THEN CONV_TAC NUM_REDUCE_CONV);;

let SI65_HPOLY v k = mk_comb(mk_comb(`mld_poly_of`,v),mk_small_numeral k);;

let SI65_WEQ = mk_forall(`j:num`,mk_imp(`j < 1536`,
  mk_eq(mk_comb(SI65_HV3,`j:num`),mk_comb(SI65_W,`j:num`))));;

let SI65_WEQ_TAC =
  SUBGOAL_THEN SI65_WEQ ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`6`; `5`; `rho:num`;
                  `mld_sign_y mld_poly_uniform_gamma1_19 RHO (5 * att)`; `j:num`]
                 MLD_LAZY_SIGN_W) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    ASM_REWRITE_TAC[MLD_LAZY_SIGN_Y_BOUND];
    ALL_TAC];;

let SI65_W_TAC k =
  let old = SI65_HPOLY SI65_HV3 k and nw = SI65_HPOLY SI65_W k in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_forall c && can (find_term ((=) old)) c then
      let iv,_ = dest_forall c in
      SUBGOAL_THEN (subst [nw,old] c) ASSUME_TAC THENL
       [X_GEN_TAC iv THEN DISCH_THEN(fun ith ->
          REWRITE_TAC[MP (SPEC iv th) ith] THEN REWRITE_TAC[mld_poly_of] THEN
          FIRST_ASSUM(fun wth -> if concl wth = SI65_WEQ then MATCH_MP_TAC wth
                                 else NO_TAC) THEN
          MP_TAC ith THEN ARITH_TAC);
        ALL_TAC]
    else NO_TAC);;

(*** Row k at fp + 3904 + 1024 k as the offset loops (base x24 = fp + 3904) ***)
(*** state it, and back                                                      ***)

let SI65_ROW_EQS = map (fun k ->
  prove(parse_term(Printf.sprintf
    "!i. word_add (word_add fp (word 3904)) (word (%d + 4 * i)):int64 =
         word_add fp (word (%d + 4 * i))" (1024 * k) (3904 + 1024 * k)),
   GEN_TAC THEN REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE)) (1--5);;

let SI65_NEST_TAC k v =
  let eqth = el (k - 1) SI65_ROW_EQS in
  let pat = parse_term(Printf.sprintf "word_add fp (word (%d + 4 * i)):int64"
                                      (3904 + 1024 * k)) in
  FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) pat)) (concl th) &&
                           can (find_term ((=) v)) (concl th)
    then ASSUME_TAC(REWRITE_RULE[GSYM eqth] th) else NO_TAC);;

let SI65_CROW_EQS = map (fun k ->
  prove(parse_term(Printf.sprintf
    "!i. word_add fp (word (3904 + %d + 4 * i)):int64 = word_add fp (word (%d + 4 * i))"
    (1024 * k) (3904 + 1024 * k)),
   GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC)) (1--5);;

let SI65_CNEST_TAC k v =
  let eqth = el (k - 1) SI65_CROW_EQS in
  let pat = parse_term(Printf.sprintf "word_add fp (word (%d + 4 * i)):int64"
                                      (3904 + 1024 * k)) in
  FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) pat)) (concl th) &&
                           can (find_term ((=) v)) (concl th)
    then ASSUME_TAC(REWRITE_RULE[GSYM eqth] th) else NO_TAC);;

let SI65_ASM_RW_TAC ths =
  RULE_ASSUM_TAC(fun th ->
    if can (find_term (fun t -> is_const t && fst(dest_const t) = "ensures")) (concl th)
    then th else REWRITE_RULE ths th);;

let SI65_FLAT_TAC = SI65_ASM_RW_TAC (SI65_ROW_EQS @ SI65_CROW_EQS);;

let SI65_HCALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc SI65_HPOST_EXEC
    name ilist [`fp:int64`; `guard:int64`; `mf:int64`; `mc:int64`; `pc:num`; `C:num`] n;;

let SI65_FPK k = parse_term(Printf.sprintf "word_add fp (word %d):int64" (3904 + 1024 * k));;

let SI65_REPOLY_MAP_TAC f v1 v2 k =
  MLD_LAZY_REPOLY_TAC (mk_comb(f,SI65_HPOLY v1 k)) (SI65_HPOLY v2 k)
    [MLD_POLY_OF_POLYVEC_MAP];;

let SI65_HPOST_CALLEES ms mcp =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    (MATCH_MP MLDSA_NATIVE_H_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL mcp)
    "H_H65" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    (MATCH_MP MLDSA_NATIVE_POLY_CHALLENGE_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL ms)
    "H_CHAL" THEN
  MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
   ([MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_NTT";
     MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_INV"] @
    map (fun k -> SI65_LK SI65_RED ("loop" ^ string_of_int (18 + k)),
                  "H_RED" ^ string_of_int k) (0--5) @
    map (fun k -> SI65_LK SI65_CADDQ ("loop" ^ string_of_int (24 + k)),
                  "H_CADDQ" ^ string_of_int k) (0--5) @
    map (fun k -> SI65_LK SI65_DEC ("mldsa65_signature_internal_loop" ^ string_of_int (30 + k)),
                  "H_DEC" ^ string_of_int k) (0--5) @
    map (fun k -> el k SI65_W1PS, "H_W1PS" ^ string_of_int k) (0--5));;

(*** The reduce loop of row 5 (loop23) states x24 = a + 1024 and the row  ***)
(*** at a + 6144 (here x24 = fp + 3904, so a = fp + 2880). The simulation   ***)
(*** of the call leaves the row as a conjunct before the events, in that   ***)
(*** nested form: prove it from the flat fact, then the events as           ***)
(*** FULL_CALL_TAC does.                                                     ***)

let SI65_RED5_EQS = map (fun tm -> prove(tm, GEN_TAC THEN REWRITE_TAC[WORD_ADD] THEN
                                             CONV_TAC WORD_RULE))
 [`!i. word_add (word_add fp (word 2880)) (word (6144 + 4 * i)):int64 =
       word_add fp (word (9024 + 4 * i))`;
  `!i. word_add (word_add (word_add fp (word 2880)) (word 6144)) (word (4 * i)):int64 =
       word_add fp (word (9024 + 4 * i))`];;

let SI65_HCALL_RED5_TAC n =
  REMOVE_THEN "H_RED5" (fun th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,SI65_HPOST_EXEC,0x0,
       mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,th)
      [`e:(uarch_event)list`; `word_add fp (word 2880):int64`; SI65_HPOLY SI65_HV 5;
       `pc:num`] n THENL
     [REPEAT(CONJ_TAC THENL
        [CONV_TAC WORD_RULE ORELSE
         (REWRITE_TAC SI65_RED5_EQS THEN FIRST_ASSUM MATCH_ACCEPT_TAC);
         ALL_TAC]) THEN
      FULL_EXISTS_E2_TAC
       (ref [`fp:int64`; `guard:int64`; `mf:int64`; `mc:int64`; `pc:num`; `C:num`]);
      LABEL_TAC "H_RED5" th]);;

let SI65_HPOST_RED_TAC k n =
  (if k = 0 || k = 5 then ALL_TAC else SI65_NEST_TAC k (SI65_HPOLY SI65_HV k)) THEN
  (if k = 5 then SI65_HCALL_RED5_TAC n
   else SI65_HCALL_TAC ("H_RED" ^ string_of_int k)
          [SI65_FPK 0; SI65_HPOLY SI65_HV k; `pc:num`] n) THEN
  SI65_FLAT_TAC THEN SI65_ASM_RW_TAC SI65_RED5_EQS THEN
  SI65_REPOLY_MAP_TAC `mld_poly_reduce` SI65_HV SI65_HV1 k;;

let SI65_HPOST_INV_TAC k n =
  SI65_HCALL_TAC "H_INV" [`read X0 s`; SI65_HPOLY SI65_HV1 k; `pc:num`;
                          `read SP s`; `read X30 s`] n THEN
  SI65_REPOLY_MAP_TAC `mld_poly_invntt_tomont` SI65_HV1 SI65_HV2 k;;

let SI65_HPOST_CADDQ_TAC k n =
  (if k = 0 then ALL_TAC else SI65_CNEST_TAC k (SI65_HPOLY SI65_YVL k)) THEN
  SI65_HCALL_TAC ("H_CADDQ" ^ string_of_int k) [SI65_FPK 0; SI65_HPOLY SI65_YVL k; `pc:num`] n THEN
  SI65_FLAT_TAC THEN
  SI65_REPOLY_MAP_TAC `mld_poly_caddq` SI65_YVL SI65_HV3 k THEN SI65_W_TAC k;;

let SI65_HPOST_PART1_TAC =
  MAP_EVERY (fun k -> MLD_LAZY_REPOLY_TAC
     (list_mk_comb(`mld_lazy_acc`,[`rho:num`; mk_small_numeral k; SI65_YH; `4`]))
     (SI65_HPOLY SI65_HV k) [MLD_POLY_OF_POLYVEC]) (0--5) THEN
  ARM_STEPS_TAC SI65_HPOST_EXEC (1--10) THEN SI65_HPOST_RED_TAC 0 11 THEN
  ARM_STEPS_TAC SI65_HPOST_EXEC (12--14) THEN SI65_HPOST_RED_TAC 1 15 THEN
  ARM_STEPS_TAC SI65_HPOST_EXEC [16] THEN SI65_HPOST_RED_TAC 2 17 THEN
  ARM_STEPS_TAC SI65_HPOST_EXEC [18] THEN SI65_HPOST_RED_TAC 3 19 THEN
  ARM_STEPS_TAC SI65_HPOST_EXEC [20] THEN SI65_HPOST_RED_TAC 4 21 THEN
  ARM_STEPS_TAC SI65_HPOST_EXEC [22] THEN SI65_HPOST_RED_TAC 5 23 THEN
  ARM_STEPS_TAC SI65_HPOST_EXEC (24--25) THEN SI65_HPOST_INV_TAC 0 26 THEN
  ARM_STEPS_TAC SI65_HPOST_EXEC (27--28) THEN SI65_HPOST_INV_TAC 1 29 THEN
  ARM_STEPS_TAC SI65_HPOST_EXEC (30--31) THEN SI65_HPOST_INV_TAC 2 32 THEN
  ARM_STEPS_TAC SI65_HPOST_EXEC (33--34) THEN SI65_HPOST_INV_TAC 3 35 THEN
  ARM_STEPS_TAC SI65_HPOST_EXEC (36--37) THEN SI65_HPOST_INV_TAC 4 38 THEN
  ARM_STEPS_TAC SI65_HPOST_EXEC (39--40) THEN SI65_HPOST_INV_TAC 5 41 THEN
  SI65_ASM_RW_TAC[GSYM SI65_YVL_EQ] THEN
  ARM_STEPS_TAC SI65_HPOST_EXEC (42--44) THEN SI65_HPOST_CADDQ_TAC 0 45 THEN
  ARM_STEPS_TAC SI65_HPOST_EXEC (46--53) THEN SI65_HPOST_CADDQ_TAC 1 54 THEN
  SI65_HPOST_CADDQ_TAC 2 55 THEN SI65_HPOST_CADDQ_TAC 3 56 THEN
  ARM_STEPS_TAC SI65_HPOST_EXEC [57] THEN
  SI65_HPOST_CADDQ_TAC 4 58 THEN SI65_HPOST_CADDQ_TAC 5 59;;

let SI65_HPOST_SETUP_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    let ms,mcp = CONJ_PAIR th in SI65_HPOST_CALLEES ms mcp) THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(fp:int64) (guard:int64) (mf:int64) (mc:int64) (pc:num) (C:num).
      f_ev_hpost fp guard mf mc pc C:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `fp:int64`; `rho:num`; `RHO:num`; `MU:num`;
                       `att:num`; `C:num`; `guard:int64`; `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; fst SI65_HPOST_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SI65_ALIGNED16_32) THEN
  SI65_WEQ_TAC THEN
  FULL_INIT_TAC;;

(*** The six rows of w0 and of w1 packed joined into the vectors ***)

let SI65_ROWS_JOIN = prove
 (`!(f:(num->int32)->num->int32) (W:num->int32) (fp:int64) (s:armstate).
     (!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (3904 + 4 * i)))) s =
                      f (mld_poly_of W 0) i) /\
     (!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (4928 + 4 * i)))) s =
                      f (mld_poly_of W 1) i) /\
     (!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (5952 + 4 * i)))) s =
                      f (mld_poly_of W 2) i) /\
     (!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (6976 + 4 * i)))) s =
                      f (mld_poly_of W 3) i) /\
     (!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (8000 + 4 * i)))) s =
                      f (mld_poly_of W 4) i) /\
     (!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (9024 + 4 * i)))) s =
                      f (mld_poly_of W 5) i)
     ==> !i. i < 1536 ==> read (memory :> bytes32 (word_add fp (word (3904 + 4 * i)))) s =
                          mld_polyvec_map f W i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?k j. k < 6 /\ j < 256 /\ i = 256 * k + j` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC [`i DIV 256`; `i MOD 256`] THEN
    MP_TAC(SPECL [`i:num`; `256`] DIVISION) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MLD_POLYVEC_MAP_COEFF] THEN
  UNDISCH_TAC `k < 6` THEN SPEC_TAC(`k:num`,`k:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `3904 + 4 * (256 + j) = 4928 + 4 * j`;
              ARITH_RULE `3904 + 4 * (512 + j) = 5952 + 4 * j`;
              ARITH_RULE `3904 + 4 * (768 + j) = 6976 + 4 * j`;
              ARITH_RULE `3904 + 4 * (1024 + j) = 8000 + 4 * j`;
              ARITH_RULE `3904 + 4 * (1280 + j) = 9024 + 4 * j`; ADD_CLAUSES] THEN
  ASM_SIMP_TAC[]);;

let SI65_W1_JOIN = prove
 (`!(W:num->int32) (fp:int64) (s:armstate).
     (!j. j < 128 ==> read (memory :> bytes8 (word_add fp (word (10048 + j)))) s =
          mld_polyw1_pack_32 (mld_poly_decompose_hi_32 (mld_poly_of W 0)) j) /\
     (!j. j < 128 ==> read (memory :> bytes8 (word_add fp (word (10176 + j)))) s =
          mld_polyw1_pack_32 (mld_poly_decompose_hi_32 (mld_poly_of W 1)) j) /\
     (!j. j < 128 ==> read (memory :> bytes8 (word_add fp (word (10304 + j)))) s =
          mld_polyw1_pack_32 (mld_poly_decompose_hi_32 (mld_poly_of W 2)) j) /\
     (!j. j < 128 ==> read (memory :> bytes8 (word_add fp (word (10432 + j)))) s =
          mld_polyw1_pack_32 (mld_poly_decompose_hi_32 (mld_poly_of W 3)) j) /\
     (!j. j < 128 ==> read (memory :> bytes8 (word_add fp (word (10560 + j)))) s =
          mld_polyw1_pack_32 (mld_poly_decompose_hi_32 (mld_poly_of W 4)) j) /\
     (!j. j < 128 ==> read (memory :> bytes8 (word_add fp (word (10688 + j)))) s =
          mld_polyw1_pack_32 (mld_poly_decompose_hi_32 (mld_poly_of W 5)) j)
     ==> !j. j < 768 ==> read (memory :> bytes8 (word_add fp (word (10048 + j)))) s =
             mld_sign_w1 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128 W j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?k j. k < 6 /\ j < 128 /\ t = 128 * k + j` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC [`t DIV 128`; `t MOD 128`] THEN
    MP_TAC(SPECL [`t:num`; `128`] DIVISION) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[mld_sign_w1; MLD_POLYVEC_PACK_COEFF; o_THM] THEN
  UNDISCH_TAC `k < 6` THEN SPEC_TAC(`k:num`,`k:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `10048 + 128 + j = 10176 + j`;
              ARITH_RULE `10048 + 256 + j = 10304 + j`;
              ARITH_RULE `10048 + 384 + j = 10432 + j`;
              ARITH_RULE `10048 + 512 + j = 10560 + j`;
              ARITH_RULE `10048 + 640 + j = 10688 + j`; ADD_CLAUSES] THEN
  ASM_SIMP_TAC[]);;

let SI65_HPOST_DEC_TAC k n =
  (if k = 0 then ALL_TAC else SI65_NEST_TAC k (SI65_HPOLY SI65_W k)) THEN
  SI65_HCALL_TAC ("H_DEC" ^ string_of_int k) [SI65_FPK 0; `word_add fp (word 10816):int64`;
     SI65_HPOLY SI65_W k; `pc:num`] n THEN SI65_FLAT_TAC;;

let SI65_HPOST_W1PS_TAC k n =
  SI65_HCALL_TAC ("H_W1PS" ^ string_of_int k) [`fp:int64`;
     mk_comb(`mld_poly_decompose_hi_32`,SI65_HPOLY SI65_W k); `pc:num`] n;;

let SI65_W1N = mk_comb(`num_of_bytelist`,list_mk_comb(`list_of_seq:(num->byte)->num->byte list`,
                                                     [SI65_W1; `768`]));;

let SI65_CT_EQ = prove
 (mk_eq(list_mk_comb(`mld_shake256_byte`,[`64 + 768 + 0`;
    list_mk_comb(`(+):num->num->num`,[`MU:num`;
      list_mk_comb(`( * ):num->num->num`,[`2 EXP (8 * 64)`;
        list_mk_comb(`(+):num->num->num`,[SI65_W1N; `2 EXP (8 * 768) * 0`])])])]),
        SI65_CT),
  REWRITE_TAC[mld_sign_ctilde] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]);;

let SI65_HPOST_PART2_TAC =
  ARM_STEPS_TAC SI65_HPOST_EXEC [60] THEN
  SI65_HPOST_DEC_TAC 0 61 THEN SI65_HPOST_W1PS_TAC 0 62 THEN
  SI65_HPOST_DEC_TAC 1 63 THEN SI65_HPOST_W1PS_TAC 1 64 THEN
  SI65_HPOST_DEC_TAC 2 65 THEN SI65_HPOST_W1PS_TAC 2 66 THEN
  SI65_HPOST_DEC_TAC 3 67 THEN SI65_HPOST_W1PS_TAC 3 68 THEN
  SI65_HPOST_DEC_TAC 4 69 THEN SI65_HPOST_W1PS_TAC 4 70 THEN
  SI65_HPOST_DEC_TAC 5 71 THEN SI65_HPOST_W1PS_TAC 5 72 THEN
  (*** w1 packed as one string, and mld_H65 for c~ ***)
  MP_TAC(SPECL [SI65_W; `fp:int64`; `s72:armstate`] SI65_W1_JOIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`fp:int64`; `10048`; `768`; SI65_W1; `s72:armstate`]
               SIGN_READ_BYTES_OF_BYTES8_OFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ARM_STEPS_TAC SI65_HPOST_EXEC [73] THEN
  SUBGOAL_THEN `read (memory :> bytes(word 0,0)) s73 = 0` ASSUME_TAC THENL
   [REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL]; ALL_TAC] THEN
  SUBGOAL_THEN `nonoverlapping_modulo (2 EXP 64) (val (word_sub fp (word 544):int64),544) (0,0)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_MODULO_TRIVIAL THEN REWRITE_TAC[]; ALL_TAC] THEN
  SI65_HCALL_TAC "H_H65" [`read X0 s`; `48`; `read X2 s`; `64`; `read X4 s`; `768`;
     `word 0:int64`; `0`; `MU:num`; SI65_W1N; `0`; `guard:int64`; `pc:num`;
     `read SP s`; `read X30 s`] 74 THEN
  MLD_WRAP_EMPTY_REGIONS_TAC THEN
  SI65_ASM_RW_TAC[SI65_CT_EQ] THEN
  SI65_ASM_RW_TAC[ASSUME (mk_eq(SI65_CTN,`C:num`))] THEN
  ARM_STEPS_TAC SI65_HPOST_EXEC (75--78) THEN
  SI65_HCALL_TAC "H_CHAL" [`read X0 s`; `read X1 s`; `C:num`; `guard:int64`; `pc:num`;
     `read SP s`; `read X30 s`] 79 THEN
  ARM_STEPS_TAC SI65_HPOST_EXEC (80--81) THEN
  SI65_HCALL_TAC "H_NTT" [`read X0 s`; `mld_poly_challenge 49 48 C`;
     `pc:num`; `read SP s`; `read X30 s`] 82 THEN
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_forall c && can (find_term ((=) `mld_poly_challenge 49 48 C`)) c &&
       not(can (find_term (fun t -> is_const t && fst(dest_const t) = "ensures")) c)
    then REWRITE_RULE[GSYM mld_sign_cphat]
           (REWRITE_RULE[SYM(ASSUME (mk_eq(SI65_CTN,`C:num`)))] th)
    else th) THEN
  MP_TAC(SPECL [`mld_poly_decompose_lo_32`; SI65_W; `fp:int64`; `s82:armstate`]
               SI65_ROWS_JOIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SI65_END_TAC;;

let SI65_HPOST = prove
 (SI65_HPOST_STMT,
  SI65_HPOST_SETUP_TAC THEN SI65_HPOST_PART1_TAC THEN SI65_HPOST_PART2_TAC);;

(* ------------------------------------------------------------------------- *)
(* A column of the loop over y (YCOL), from loop3 with the column j in w23:  *)
(* y_j sampled (the inlined poly_uniform_gamma1, nonce 5 att + j) at         *)
(* fp + 10816 and transformed, then for each row i the entry (i,j) of the    *)
(* matrix sampled by poly_uniform from the seed rho || j || i at fp + 12160. *)
(* For j > 0 (SI65_YCOLJ, j = n + 1) its product with y^_j at fp + 544 is    *)
(* added to row i; for j = 0 (SI65_YCOL0) the entry is sampled into row i    *)
(* and multiplied in place. Row i then holds mld_lazy_acc rho i y^ j.        *)
(* ------------------------------------------------------------------------- *)

let SI65_SEED = prove
 (`!fp rho i j (s:armstate).
     read (memory :> bytes(word_add fp (word 12160),32)) s = rho /\
     read (memory :> bytes8 (word_add fp (word 12192))) s = word j /\
     read (memory :> bytes8 (word_add fp (word 12193))) s = word i /\
     i < 256 /\ j < 256
     ==> read (memory :> bytes(word_add fp (word 12160),34)) s = mld_matrix_seed rho i j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mld_matrix_seed] THEN
  REWRITE_TAC[ARITH_RULE `34 = 32 + 1 + 1`; READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  CONV_TAC(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[READ_MEMORY_BYTES_BYTES8] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC);;

let SI65_ACC_SUC = prove
 (`!rho i (v:num->int32) n.
     mld_lazy_acc rho i v (n + 1) =
     mld_poly_add (mld_lazy_acc rho i v n)
      (mld_poly_pointwise_montgomery (mld_poly_uniform (mld_matrix_seed rho i (n + 1)))
                                     (mld_poly_of v (n + 1)))`,
  REWRITE_TAC[GSYM ADD1; mld_lazy_acc; mld_matrix_entry]);;

let SI65_ACC_ROWS_N n = String.concat " /\\\n" (map (fun k -> Printf.sprintf
  "(!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (%d + 4 * i)))) s =
                   mld_lazy_acc rho %d (%s) %s i)" (3904 + 1024 * k) k
  (string_of_term SI65_YH) n) (0--5));;

let SI65_YCOL_PRE =
 "read SP s = fp /\\
  read X20 s = word_add fp (word 10816) /\\ read X21 s = word_add fp (word 11936) /\\
  read X24 s = word_add fp (word 3904) /\\
  read X26 s = word 18446744073701171199 /\\ read X19 s = word 252236767799803904 /\\
  read X28 s = word_add fp (word 10824) /\\
  read (memory :> bytes64 (word_add fp (word 328))) s = word_add fp (word 9036) /\\
  read (memory :> bytes64 (word_add fp (word 336))) s = word_add fp (word 8012) /\\
  read (memory :> bytes64 (word_add fp (word 344))) s = word_add fp (word 9024) /\\
  read (memory :> bytes64 (word_add fp (word 408))) s = word_add fp (word 10057) /\\
  read (memory :> bytes32 (word_add fp (word 416))) s = word (5 * att) /\\
  read (memory :> bytes64 (word_add fp (word 440))) s = word_add fp (word 1792) /\\
  read (memory :> bytes (word_add fp (word 1792),64)) s = RHO /\\
  read (memory :> bytes (word_add fp (word 12160),32)) s = rho /\\
  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s = guard /\\
  read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
  read (memory :> bytes(ea,el)) s = ev";;

let SI65_YCOL_MC =
 "MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
  MAYCHANGE [X18; X21; X22; X23; X24; X25; X27; X30] ,,
  MAYCHANGE [memory :> bytes(word_sub fp (word 1472),1472);
             memory :> bytes(word_add fp (word 544),1024);
             memory :> bytes(word_add fp (word 3904),6144);
             memory :> bytes(word_add fp (word 10048),680);
             memory :> bytes(word_add fp (word 10816),1024);
             memory :> bytes(word_add fp (word 11936),66);
             memory :> bytes(word_add fp (word 12192),2);
             memory :> bytes(word_add fp (word 12256),208)]";;

let SI65_YCOL_EV =
 "memaccess_inbounds e2
   [word_sub fp (word 1472),14432;
    word(pc + got_stack_chk_guard),8; guard,8;
    word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
    word(pc + rodata_mld_KeccakF_RoundConstants),192;
    word(pc + rodata_mld_zetas),1024;
    word(pc + mldsa65_signature_internal_consts),336]
   [word_sub fp (word 1472),14432]";;

let SI65_YCOLJ_STMT = parse_term(
 "!mf mc ea el ev.
   memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
   ==> exists f_events.
        forall e fp rho RHO att n guard pc.
         aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
         aligned 32 fp /\\ att < 13106 /\\ n < 4 /\\ mld_matrix_terminates 6 5 rho /\\
         ALL (nonoverlapping (word_sub fp (word 1472),14432))
             [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8); (guard,8);
              (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
         ==> ensures arm
              (\\s. aligned_bytes_loaded s (word pc)
                     mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                   read PC s = word (pc + mldsa65_signature_internal_loop3) /\\
                   read X23 s = word (n + 1) /\\\n" ^ SI65_YCOL_PRE ^ " /\\\n" ^
  SI65_ACC_ROWS_N "n" ^ " /\\
                   read events s = e)
              (\\s. read PC s = (if n + 2 < 5 then word (pc + mldsa65_signature_internal_loop3)
                                else word (pc + mldsa65_signature_internal_loop3_exit)) /\\
                   read SP s = fp /\\ read X23 s = word (n + 2) /\\
                   read X21 s = word_add fp (word 11936) /\\
                   read X24 s = word_add fp (word 3904) /\\\n" ^
  SI65_ACC_ROWS_N "(n + 1)" ^ " /\\
                   (exists e2.
                      read events s = APPEND e2 e /\\
                      e2 = f_events fp rho n guard mf mc pc /\\ " ^ SI65_YCOL_EV ^ "))
              (" ^ SI65_YCOL_MC ^ ")");;

let SI65_YCOL_EXEC = SI65_EXEC_RANGE "join3" "loop3_exit";;

let SI65_ZX8 = prove
 (`!k. k < 256 ==> word_zx (word k:int64):byte = word k`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `k MOD 256 = k /\ k MOD 18446744073709551616 = k` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_REWRITE_TAC[]]);;

let SI65_COLNZ = prove
 (`!n. n < 4 ==> ~(val (word_zx (word (n + 1):int64):int32) = 0)`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let SI65_PU_PRE_TAC i jt st =
  MP_TAC(SPECL [`fp:int64`; `rho:num`; mk_small_numeral i; jt; st] SI65_SEED) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `n + 1 < 256` ASSUME_TAC THENL
     [UNDISCH_TAC `n < 4` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SI65_ZX_BYTE; SI65_ZX8] THEN UNDISCH_TAC `n < 4` THEN ARITH_TAC;
    DISCH_TAC] THEN
  FIRST_ASSUM(fun th -> if can (term_match [] `mld_matrix_terminates 6 5 r`) (concl th) then
    MP_TAC(SPECL [mk_small_numeral i; jt] (REWRITE_RULE[mld_matrix_terminates] th)) THEN
    ANTS_TAC THENL [UNDISCH_TAC `n < 4` THEN ARITH_TAC; DISCH_TAC] else NO_TAC);;

let SI65_YCOL_ALLOWED = [`fp:int64`; `rho:num`; `n:num`; `guard:int64`; `mf:int64`;
                         `mc:int64`; `pc:num`];;

let SI65_YCOL_CALL_TAC name ilist k =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc SI65_YCOL_EXEC name
    ilist SI65_YCOL_ALLOWED k;;

let SI65_YY k = mk_comb(mk_comb(`mld_poly_of`,
  `mld_sign_y mld_poly_uniform_gamma1_19 RHO (5 * att)`),k);;
let SI65_YHK k = mk_comb(mk_comb(`mld_poly_of`,SI65_YH),k);;
let SI65_ACC i nt = list_mk_comb(`mld_lazy_acc`,[`rho:num`; mk_small_numeral i; SI65_YH; nt]);;
let SI65_ENT i jt = mk_comb(`mld_poly_uniform`,
  list_mk_comb(`mld_matrix_seed`,[`rho:num`; mk_small_numeral i; jt]));;
let SI65_PWT i jt = list_mk_comb(`mld_poly_pointwise_montgomery`,[SI65_ENT i jt; SI65_YHK jt]);;

let SI65_FR_Y = SI65_FR_EQS [240; 656; 680; 648; 10297; 11056; 12176; 12496; 10288; 4144]
                            [11056; 10288];;

let SI65_YCOL_CALLEES th =
  ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP SI65_G1_Y th) "H_G1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    (MATCH_MP MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL th)
    "H_PU" THEN
  MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
   ([MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_NTT"] @
    map (fun k -> SI65_LK SI65_PWM ("loop" ^ string_of_int (6 + k)),
                  "H_PWM" ^ string_of_int k) (0--5) @
    map (fun k -> el k SI65_ADDS, "H_ADD" ^ string_of_int k) (0--5) @
    map (fun k -> SI65_LK SI65_PWM ("loop" ^ string_of_int (12 + k)),
                  "H_PWMZ" ^ string_of_int k) (0--5));;

(*** y_j (index jt, nonce 5 att + jt) and its NTT, up to the branch on j ***)

let SI65_YCOL_Y_TAC jt =
  MAP_EVERY ASSUME_TAC SI65_FR_Y THEN
  SI65_YCOL_CALL_TAC "H_G1" [`word_add fp (word 1792):int64`; `RHO:num`; `5 * att`; jt;
    `word_sub fp (word 240):int64`; `pc:num`] 1 THEN
  SI65_ASM_RW_TAC SI65_FR_Y THEN
  MLD_LAZY_REPOLY_TAC
    (list_mk_comb(`mld_poly_uniform_gamma1_19`,
      [`RHO:num`; mk_comb(`word:num->int16`,mk_binop `(+):num->num->num` `5 * att` jt)]))
    (SI65_YY jt) [mld_sign_y; MLD_POLY_OF_POLYVEC] THEN
  ARM_STEPS_TAC SI65_YCOL_EXEC (2--16) THEN
  SI65_YCOL_CALL_TAC "H_NTT" [`read X0 s`; SI65_YY jt; `pc:num`; `read SP s`;
                              `read X30 s`] 17 THEN
  MLD_LAZY_REPOLY_TAC (mk_comb(`mld_poly_ntt`,SI65_YY jt)) (SI65_YHK jt)
    [MLD_POLY_OF_POLYVEC_MAP] THEN
  ARM_STEPS_TAC SI65_YCOL_EXEC (18--19);;

(*** Row i of a column j > 0, the call of poly_uniform being step n0 ***)

let SI65_YCOLJ_ROW_TAC i n0 =
  let jt = `n + 1` in
  (if i = 0 then ALL_TAC else ARM_STEPS_TAC SI65_YCOL_EXEC [n0 - 1]) THEN
  SI65_PU_PRE_TAC i jt (mk_var("s"^string_of_int (n0-1),`:armstate`)) THEN
  SI65_YCOL_CALL_TAC "H_PU" [`read X0 s`; `read X1 s`;
    list_mk_comb(`mld_matrix_seed`,[`rho:num`; mk_small_numeral i; jt]);
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] n0 THEN
  ARM_STEPS_TAC SI65_YCOL_EXEC [n0 + 1] THEN
  SI65_YCOL_CALL_TAC ("H_PWM" ^ string_of_int i)
    [`word_add fp (word 544):int64`; `word_add fp (word 10816):int64`;
     SI65_ENT i jt; SI65_YHK jt; `pc:num`] (n0 + 2) THEN
  SI65_YCOL_CALL_TAC ("H_ADD" ^ string_of_int i)
    ([`fp:int64`; SI65_ACC i `n:num`; SI65_PWT i jt] @
     (if i < 5 then [jt] else []) @ [`pc:num`]) (n0 + 3) THEN
  SI65_ASM_RW_TAC[GSYM SI65_ACC_SUC];;

let SI65_COLINC = prove
 (`!n. n < 4
       ==> word_zx (word_add (word_zx (word (n + 1):int64):int32) (word 1)):int64 =
           word (n + 2)`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV);;

let SI65_COLTEST = prove
 (`!n. n < 4
       ==> (val (word_sub (word_zx (word (n + 2):int64):int32) (word 5)) = 0 <=>
            ~(n + 2 < 5))`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let SI65_YCOLJ = prove
 (SI65_YCOLJ_STMT,
  REPEAT GEN_TAC THEN DISCH_THEN SI65_YCOL_CALLEES THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(fp:int64) (rho:num) (n:num) (guard:int64) (mf:int64) (mc:int64) (pc:num).
      if n + 2 < 5 then f_ev_mid fp rho n guard mf mc pc
      else f_ev_last fp rho n guard mf mc pc:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `fp:int64`; `rho:num`; `RHO:num`; `att:num`;
                       `n:num`; `guard:int64`; `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; fst SI65_YCOL_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SI65_ALIGNED16_32) THEN
  FULL_INIT_TAC THEN SI65_YCOL_Y_TAC `n + 1` THEN
  SI65_ASM_RW_TAC[MP (SPEC `n:num` SI65_COLNZ) (ASSUME `n < 4`)] THEN
  ARM_STEPS_TAC SI65_YCOL_EXEC (20--25) THEN
  SI65_YCOLJ_ROW_TAC 0 26 THEN SI65_YCOLJ_ROW_TAC 1 31 THEN
  SI65_YCOLJ_ROW_TAC 2 36 THEN SI65_YCOLJ_ROW_TAC 3 41 THEN
  SI65_YCOLJ_ROW_TAC 4 46 THEN SI65_YCOLJ_ROW_TAC 5 51 THEN
  ARM_STEPS_TAC SI65_YCOL_EXEC (55--58) THEN
  SI65_ASM_RW_TAC[MP (SPEC `n:num` SI65_COLINC) (ASSUME `n < 4`)] THEN
  SI65_ASM_RW_TAC[MP (SPEC `n:num` SI65_COLTEST) (ASSUME `n < 4`)] THEN
  SI65_CASES_TAC `n + 2 < 5` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SI65_END_TAC);;

(*** The column j = 0 ***)

(*** Column 0 needs neither x21 nor x24: the sampling of y sets both ***)

let SI65_YCOL0_PRE =
 "read SP s = fp /\\
  read X20 s = word_add fp (word 10816) /\\
  read X26 s = word 18446744073701171199 /\\ read X19 s = word 252236767799803904 /\\
  read X28 s = word_add fp (word 10824) /\\
  read (memory :> bytes64 (word_add fp (word 328))) s = word_add fp (word 9036) /\\
  read (memory :> bytes64 (word_add fp (word 336))) s = word_add fp (word 8012) /\\
  read (memory :> bytes64 (word_add fp (word 344))) s = word_add fp (word 9024) /\\
  read (memory :> bytes64 (word_add fp (word 408))) s = word_add fp (word 10057) /\\
  read (memory :> bytes32 (word_add fp (word 416))) s = word (5 * att) /\\
  read (memory :> bytes64 (word_add fp (word 440))) s = word_add fp (word 1792) /\\
  read (memory :> bytes (word_add fp (word 1792),64)) s = RHO /\\
  read (memory :> bytes (word_add fp (word 12160),32)) s = rho /\\
  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s = guard /\\
  read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
  read (memory :> bytes(ea,el)) s = ev";;

let SI65_YCOL0_STMT = parse_term(
 "!mf mc ea el ev.
   memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
   ==> exists f_events.
        forall e fp rho RHO att guard pc.
         aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
         aligned 32 fp /\\ att < 13106 /\\ mld_matrix_terminates 6 5 rho /\\
         ALL (nonoverlapping (word_sub fp (word 1472),14432))
             [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8); (guard,8);
              (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
         ==> ensures arm
              (\\s. aligned_bytes_loaded s (word pc)
                     mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                   read PC s = word (pc + mldsa65_signature_internal_loop3) /\\
                   read X23 s = word 0 /\\\n" ^ SI65_YCOL0_PRE ^ " /\\
                   read events s = e)
              (\\s. read PC s = word (pc + mldsa65_signature_internal_loop3) /\\
                   read SP s = fp /\\ read X23 s = word 1 /\\
                   read X21 s = word_add fp (word 11936) /\\
                   read X24 s = word_add fp (word 3904) /\\\n" ^
  SI65_ACC_ROWS_N "0" ^ " /\\
                   (exists e2.
                      read events s = APPEND e2 e /\\
                      e2 = f_events fp rho guard mf mc pc /\\ " ^ SI65_YCOL_EV ^ "))
              (" ^ SI65_YCOL_MC ^ ")");;

let SI65_SEED16 = prove
 (`!fp rho i (s:armstate).
     read (memory :> bytes(word_add fp (word 12160),32)) s = rho /\
     read (memory :> bytes16 (word_add fp (word 12192))) s = word (256 * i) /\
     i < 256
     ==> read (memory :> bytes(word_add fp (word 12160),34)) s = mld_matrix_seed rho i 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mld_matrix_seed] THEN
  REWRITE_TAC[ARITH_RULE `34 = 32 + 2`; READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  CONV_TAC(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `read (memory :> bytes(word_add fp (word 12192),2)) s = val(word (256 * i):int16)`
   SUBST1_TAC THENL
   [FIRST_X_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes16 a) s = x`) (concl th)
      then REWRITE_TAC[GSYM th] else NO_TAC) THEN
    REWRITE_TAC[BYTES16_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES; DIMINDEX_16] THEN
    CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[VAL_WORD; DIMINDEX_16] THEN
    SUBGOAL_THEN `(256 * i) MOD 2 EXP 16 = 256 * i` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ARITH_TAC]]);;

let SI65_PU0_PRE_TAC i st =
  MP_TAC(SPECL [`fp:int64`; `rho:num`; mk_small_numeral i; st] SI65_SEED16) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    TRY(FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes16 a) s = x`) (concl th)
                              then REWRITE_TAC[th] THEN CONV_TAC WORD_REDUCE_CONV else NO_TAC));
    DISCH_TAC] THEN
  FIRST_ASSUM(fun th -> if can (term_match [] `mld_matrix_terminates 6 5 r`) (concl th) then
    MP_TAC(SPECL [mk_small_numeral i; `0`] (REWRITE_RULE[mld_matrix_terminates] th)) THEN
    ANTS_TAC THENL [ARITH_TAC; DISCH_TAC] else NO_TAC);;

let SI65_ACC0 = prove
 (`!rho i (v:num->int32).
     mld_lazy_acc rho i v 0 =
     mld_poly_pointwise_montgomery (mld_poly_uniform (mld_matrix_seed rho i 0))
                                   (mld_poly_of v 0)`,
  REWRITE_TAC[mld_lazy_acc; mld_matrix_entry]);;

(*** Row i of the column j = 0, the call of poly_uniform being step n0; the ***)
(*** 3 instructions before the product (ORR into x8 and x9, the pointer x10 ***)
(*** for rows 1 to 5, from the slots at fp + 336 and fp + 328 for 4 and 5)  ***)

let SI65_YCOL0_ROW_TAC i n0 =
  (if i = 0 then ALL_TAC else
     ARM_STEPS_TAC SI65_YCOL_EXEC ((n0 - 6)--(n0 - 1)) THEN
     SI65_PU0_PRE_TAC i (mk_var("s"^string_of_int (n0-1),`:armstate`))) THEN
  SI65_YCOL_CALL_TAC "H_PU" [`read X0 s`; `read X1 s`;
    list_mk_comb(`mld_matrix_seed`,[`rho:num`; mk_small_numeral i; `0`]);
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] n0 THEN
  ARM_STEPS_TAC SI65_YCOL_EXEC ((n0+1)--(n0+3)) THEN
  SI65_ASM_RW_TAC[MP (SI65_ORR_THM 10816 8) (ASSUME `aligned 32 (fp:int64)`);
                  MP (SI65_ORR_THM 3904 8) (ASSUME `aligned 32 (fp:int64)`)] THEN
  SI65_YCOL_CALL_TAC ("H_PWMZ" ^ string_of_int i)
    [SI65_FPK i; `word_add fp (word 10816):int64`; SI65_ENT i `0`; SI65_YHK `0`; `pc:num`]
    (n0 + 4) THEN
  SI65_ASM_RW_TAC[GSYM SI65_ACC0];;

let SI65_YCOL0 = prove
 (SI65_YCOL0_STMT,
  REPEAT GEN_TAC THEN DISCH_THEN SI65_YCOL_CALLEES THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(fp:int64) (rho:num) (guard:int64) (mf:int64) (mc:int64) (pc:num).
      f_ev_col0 fp rho guard mf mc pc:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `fp:int64`; `rho:num`; `RHO:num`; `att:num`;
                       `guard:int64`; `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; fst SI65_YCOL_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SI65_ALIGNED16_32) THEN
  FULL_INIT_TAC THEN SI65_YCOL_Y_TAC `0` THEN
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read PC s = x`) (concl th) then
     CONV_RULE(DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV) th else th) THEN
  ARM_STEPS_TAC SI65_YCOL_EXEC (20--24) THEN SI65_PU0_PRE_TAC 0 `s24:armstate` THEN
  SI65_YCOL0_ROW_TAC 0 25 THEN SI65_YCOL0_ROW_TAC 1 36 THEN
  SI65_YCOL0_ROW_TAC 2 47 THEN SI65_YCOL0_ROW_TAC 3 58 THEN
  SI65_YCOL0_ROW_TAC 4 69 THEN SI65_YCOL0_ROW_TAC 5 80 THEN
  ARM_STEPS_TAC SI65_YCOL_EXEC (85--88) THEN
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read PC s = x`) (concl th) ||
                              can (term_match [] `read X23 s = x`) (concl th) then
     CONV_RULE(DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV) th else th) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SI65_END_TAC);;

(* ------------------------------------------------------------------------- *)
(* The start of an attempt (HEAD), from loop2 with its number att in w10:   *)
(* att saved at fp + 76, kappa = 5 att (32 bits at fp + 416, 16 bits at      *)
(* fp + 11848) and the pointer to rho'' at fp + 11840, rho copied from       *)
(* fp + 1568 to the seed of the matrix at fp + 12160, then the five columns  *)
(* of the product with the matrix (YCOL0, YCOLJ for n = 0 .. 3) and HPOST,   *)
(* to after the NTT of the challenge.                                        *)
(* ------------------------------------------------------------------------- *)

let SI65_HEAD_PRE =
 "read SP s = fp /\\
  read X20 s = word_add fp (word 10816) /\\
  read X26 s = word 18446744073701171199 /\\ read X19 s = word 252236767799803904 /\\
  read X28 s = word_add fp (word 10824) /\\
  read (memory :> bytes64 (word_add fp (word 56))) s = word_add fp (word 1568) /\\
  read (memory :> bytes64 (word_add fp (word 328))) s = word_add fp (word 9036) /\\
  read (memory :> bytes64 (word_add fp (word 336))) s = word_add fp (word 8012) /\\
  read (memory :> bytes64 (word_add fp (word 344))) s = word_add fp (word 9024) /\\
  read (memory :> bytes64 (word_add fp (word 408))) s = word_add fp (word 10057) /\\
  read (memory :> bytes64 (word_add fp (word 440))) s = word_add fp (word 1792) /\\
  read (memory :> bytes128 (word_add fp (word 368))) s =
  word 339618401959998730991157055895298383871 /\\
  read (memory :> bytes (word_add fp (word 1568),32)) s = rho /\\
  read (memory :> bytes (word_add fp (word 1728),64)) s = MU /\\
  read (memory :> bytes (word_add fp (word 1792),64)) s = RHO /\\
  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s = guard /\\
  read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
  read (memory :> bytes(ea,el)) s = ev";;

let SI65_HEAD_MC =
 "MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
  MAYCHANGE [X18; X21; X22; X23; X24; X25; X27; X30] ,,
  MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
  MAYCHANGE [memory :> bytes(word_sub fp (word 1472),1472);
             memory :> bytes(word_add fp (word 76),4);
             memory :> bytes(word_add fp (word 80),240);
             memory :> bytes(word_add fp (word 384),16);
             memory :> bytes(word_add fp (word 416),16);
             memory :> bytes(word_add fp (word 544),1024);
             memory :> bytes(word_add fp (word 2880),1024);
             memory :> bytes(word_add fp (word 3904),6144);
             memory :> bytes(word_add fp (word 10048),768);
             memory :> bytes(word_add fp (word 10816),1024);
             memory :> bytes(word_add fp (word 11840),16);
             memory :> bytes(word_add fp (word 11872),48);
             memory :> bytes(word_add fp (word 11936),66);
             memory :> bytes(word_add fp (word 12160),64);
             memory :> bytes(word_add fp (word 12256),208)]";;

let SI65_HEAD_STMT = parse_term(
 "!mf mc ea el ev.
   memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
   ==> exists f_events.
        forall e fp att rho RHO MU C guard pc.
         aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
         aligned 32 fp /\\ att < 13106 /\\ mld_matrix_terminates 6 5 rho /\\
         " ^ string_of_term SI65_CTN ^ " = C /\\
         mld_poly_challenge_terminates 49 48 C /\\
         ALL (nonoverlapping (word_sub fp (word 1472),14432))
             [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8); (guard,8);
              (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
         ==> ensures arm
              (\\s. aligned_bytes_loaded s (word pc)
                     mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                   read PC s = word (pc + mldsa65_signature_internal_loop2) /\\
                   read X10 s = word att /\\\n" ^ SI65_HEAD_PRE ^ " /\\
                   read events s = e)
              (\\s. read PC s = word (pc + mldsa65_signature_internal_after_mldsa_poly_ntt_2) /\\
                   read SP s = fp /\\
                   read X20 s = word_add fp (word 10816) /\\
                   read X21 s = word_add fp (word 11936) /\\
                   read X22 s = word_add fp (word 1856) /\\
                   read (memory :> bytes32 (word_add fp (word 76))) s = word att /\\
                   read (memory :> bytes64 (word_add fp (word 11840))) s = word_add fp (word 1792) /\\
                   read (memory :> bytes16 (word_add fp (word 11848))) s = word (5 * att) /\\
                   (!i. i < 1536 ==> read (memory :> bytes32 (word_add fp (word (3904 + 4 * i)))) s =
                                     mld_polyvec_map mld_poly_decompose_lo_32 (" ^
                                       string_of_term SI65_W ^ ") i) /\\
                   (!j. j < 768 ==> read (memory :> bytes8 (word_add fp (word (10048 + j)))) s =
                                    " ^ string_of_term SI65_W1 ^ " j) /\\
                   read (memory :> bytes (word_add fp (word 11872),48)) s = C /\\
                   (!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (2880 + 4 * i)))) s =
                                    mld_sign_cphat 49 48 (" ^ string_of_term SI65_CT ^ ") i) /\\
                   (exists e2.
                      read events s = APPEND e2 e /\\
                      e2 = f_events fp rho C guard mf mc pc /\\
                      memaccess_inbounds e2
                       [word_sub fp (word 1472),14432;
                        word(pc + got_stack_chk_guard),8; guard,8;
                        word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                        word(pc + rodata_mld_KeccakF_RoundConstants),192;
                        word(pc + rodata_mld_zetas),1024;
                        word(pc + mldsa65_signature_internal_consts),336]
                       [word_sub fp (word 1472),14432]))
              (" ^ SI65_HEAD_MC ^ ")");;

let SI65_HEAD_EXEC = SI65_EXEC_RANGE "loop2" "after_mldsa_poly_ntt_2";;

let SI65_HEAD_ALLOWED = [`fp:int64`; `rho:num`; `C:num`; `guard:int64`; `mf:int64`;
                         `mc:int64`; `pc:num`];;

let SI65_HEAD_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc SI65_HEAD_EXEC name
    ilist SI65_HEAD_ALLOWED n;;

let SI65_ZX32 = prove
 (`!n. word_zx (word n:int64):int32 = word n`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

(*** kappa = 5 att as add w9, w10, w10, lsl #2 computes it, and as str and ***)
(*** strh store it                                                          ***)

let SI65_KAPPA = prove
 (`!att. att < 13106
         ==> word_add (word_zx (word att:int64):int32)
                      (word_shl (word_zx (word att:int64):int32) 2) = word (5 * att)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SI65_ZX32; WORD_SHL_WORD; GSYM WORD_ADD] THEN
  AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let SI65_KAPPA16 = prove
 (`!att. att < 13106 ==> word_zx (word (5 * att):int32):int16 = word (5 * att)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_16; DIMINDEX_32] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

let SI65_ZX16_64 = WORD_BLAST
 `!x:int32. word_zx (word_zx x:int64):int16 = word_zx x`;;

let SI65_HEAD_NUM_TAC =
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if can (find_term (fun t -> is_const t && fst(dest_const t) = "ensures")) c then th
    else if can (term_match [] `read PC s = x`) c || can (term_match [] `read X23 s = x`) c ||
       (is_forall c &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mld_lazy_acc")) c)
    then CONV_RULE(NUM_REDUCE_CONV THENC REWRITE_CONV[]) th else th);;

let SI65_HEAD_COL_TAC n k =
  SI65_REG_FORM_TAC "X23" (k - 1) (subst [mk_small_numeral n,`n:num`] `word (n + 1):int64`) THEN
  SI65_HEAD_CALL_TAC "H_YCJ" [`fp:int64`; `rho:num`; `RHO:num`; `att:num`; mk_small_numeral n;
                              `guard:int64`; `pc:num`] k THEN
  SI65_HEAD_NUM_TAC;;

let SI65_HEAD = prove
 (SI65_HEAD_STMT,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
     [MP (SPEC_ALL SI65_YCOL0) th,"H_YC0"; MP (SPEC_ALL SI65_YCOLJ) th,"H_YCJ";
      MP (SPEC_ALL SI65_HPOST) th,"H_HP"]) THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(fp:int64) (rho:num) (C:num) (guard:int64) (mf:int64) (mc:int64) (pc:num).
      f_ev_head fp rho C guard mf mc pc:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `fp:int64`; `att:num`; `rho:num`; `RHO:num`;
                       `MU:num`; `C:num`; `guard:int64`; `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; fst SI65_HEAD_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SI65_ALIGNED16_32) THEN
  FULL_INIT_TAC THEN
  (*** the head of loop2: att, kappa, the pointer to rho'' and rho ***)
  MAP_EVERY (fun n ->
    MP_TAC(SPECL [`word_add fp (word 1568):int64`; `32`; `rho:num`; mk_small_numeral n;
                  `s0:armstate`] SIGN_BYTES128_OF_BYTES) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC) [0;1] THEN
  ARM_STEPS_TAC SI65_HEAD_EXEC (1--2) THEN
  SI65_ASM_RW_TAC[MP (SPEC `att:num` SI65_KAPPA) (ASSUME `att < 13106`)] THEN
  ARM_STEPS_TAC SI65_HEAD_EXEC (3--14) THEN
  SI65_ASM_RW_TAC[SI65_ZX32; SI65_ZX16_64; WORD_ZX_ZX_32_64_32;
                  MP (SPEC `att:num` SI65_KAPPA16) (ASSUME `att < 13106`)] THEN
  SUBGOAL_THEN `rho < 2 EXP (8 * 32)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if can (term_match []
       `read (memory :> bytes (word_add fp (word 1568),32)) s0 = rho`) (concl th)
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[READ_BYTES_BOUND; READ_COMPONENT_COMPOSE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`word_add fp (word 12160):int64`; `rho:num`; `2`; `s14:armstate`]
               SIGN_BYTES_OF_BYTES128) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0; DIV_1] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN ASM_REWRITE_TAC[DIV_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `rho MOD 2 EXP (128 * 2) = rho` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN
    FIRST_ASSUM(MP_TAC o check (fun th -> concl th = `rho < 2 EXP (8 * 32)`)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN DISCH_TAC THEN
  (*** the five columns of A y and HPOST ***)
  SI65_HEAD_CALL_TAC "H_YC0" [`fp:int64`; `rho:num`; `RHO:num`; `att:num`; `guard:int64`;
                              `pc:num`] 15 THEN
  SI65_HEAD_COL_TAC 0 16 THEN SI65_HEAD_COL_TAC 1 17 THEN SI65_HEAD_COL_TAC 2 18 THEN
  SI65_HEAD_COL_TAC 3 19 THEN
  SI65_HEAD_CALL_TAC "H_HP" [`fp:int64`; `rho:num`; `RHO:num`; `MU:num`; `att:num`; `C:num`;
                             `guard:int64`; `pc:num`] 20 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SI65_END_TAC);;

(* ------------------------------------------------------------------------- *)
(* A whole attempt (ATT), from loop2 with its number att in w10 to the exit  *)
(* of the cleanup: to loop2_exit2 on success (r = 18), else to loop2 with    *)
(* att + 1 in w10 or, after the last attempt, to loop2_exit1. By cases on    *)
(* the result r of mld_sign_attempt_declass: r < 5 (z_r fails: ZPRE, then   *)
(* ZIT and loop36_exit2), 5 <= r < 17 (check r - 5 of the rows fails: ZPRE,  *)
(* RPRE, then RIT and join10), 17 (too many hints) and 18 (success), both    *)
(* through TAIL; then CLEAN from join12.                                     *)
(* ------------------------------------------------------------------------- *)

let SI65_ATT_CPH = `mld_poly_ntt (mld_poly_challenge 49 48 C)`;;
let SI65_ATT_W = SI65_W;;
let SI65_ATT_R0 = list_mk_comb(`mld_sign_r0`,
  [`mld_poly_decompose_lo_32`; SI65_ATT_W; SI65_S2H; SI65_ATT_CPH]);;
let SI65_ATT_CT0 = list_mk_comb(`mld_sign_ct0`,[SI65_T0H; SI65_ATT_CPH]);;
let SI65_SIGATT = list_mk_comb(
 `mld_sign_attempt_sig 6 5 48 49 mld_poly_uniform_gamma1_19 mld_polyz_pack_19
   640 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128
   mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 55`,
  [`mld_polyvec_matrix_expand 5 rho`; SI65_S1H; SI65_S2H; SI65_T0H; `MU:num`; `RHO:num`;
   `5 * att`]);;

let SI65_ATT_STMT = parse_term(
 "!mf mc ea el ev.
   memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
   ==> exists f_events.
        forall e sig sk skb fp rho MU RHO att C r x b guard pc.
         aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
         aligned 32 fp /\\ val fp + 12960 < 2 EXP 63 /\\ att < 13106 /\\
         mld_matrix_terminates 6 5 rho /\\
         mld_sign_attempt_declass 6 5 48 49 mld_poly_uniform_gamma1_19
          524092 261692 261888 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32)
          128 mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 55
          (mld_polyvec_matrix_expand 5 rho) (" ^ string_of_term SI65_S1H ^ ")
          (" ^ string_of_term SI65_S2H ^ ") (" ^ string_of_term SI65_T0H ^ ")
          MU RHO (5 * att) = (C,r,x,b) /\\
         mld_poly_challenge_terminates 49 48 C /\\
         nonoverlapping (sig,3309) (word_sub fp (word 1472),14432) /\\
         ALL (nonoverlapping (word_sub fp (word 1472),14432))
             [(sk,4032); (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
              (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\\
         ALL (nonoverlapping (sig,3309))
             [(sk,4032); (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
              (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
         ==> ensures arm
              (\\s. aligned_bytes_loaded s (word pc)
                     mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                   read PC s = word (pc + mldsa65_signature_internal_loop2) /\\
                   read X10 s = word att /\\\n" ^ SI65_HEAD_PRE ^ " /\\\n" ^
  SI65_SLOT_FACTS [24,8000; 32,6976; 40,5952; 48,4928; 320,2888; 352,12265; 360,2880] ^
 "                 read (memory :> bytes64 (word_add fp (word 64))) s = sig /\\
                   read (memory :> bytes64 (word_add fp (word 16))) s =
                   word_add sig (word 3248) /\\
                   read (memory :> bytes64 (word_add fp (word 448))) s = word_add sk (word 768) /\\
                   read (memory :> bytes64 (word_add fp (word 480))) s = word_add sk (word 1536) /\\
                   read (memory :> bytes64 (word_add fp (word 512))) s = word_add sk (word 128) /\\
                   (!i. i < 4032 ==> read (memory :> bytes8 (word_add sk (word i))) s = skb i) /\\
                   read events s = e)
              (\\s. read PC s =
                   (if r = 18 then word (pc + mldsa65_signature_internal_loop2_exit2)
                    else if att + 1 < 13106 then word (pc + mldsa65_signature_internal_loop2)
                    else word (pc + mldsa65_signature_internal_loop2_exit1)) /\\
                   read SP s = fp /\\
                   read X20 s = word_add fp (word 10816) /\\
                   (~(r = 18) ==> read X10 s = word (att + 1)) /\\
                   read (memory :> bytes64(word(pc + got_stack_chk_guard))) s = guard /\\
                   read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                   read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                   read (memory :> bytes(ea,el)) s = ev /\\
                   (r = 18
                    ==> !t. t < 3309
                            ==> read (memory :> bytes8 (word_add sig (word t))) s =
                                (" ^ string_of_term SI65_SIGATT ^ ") t) /\\
                   (exists e2.
                      read events s = APPEND e2 e /\\
                      e2 = f_events sig sk fp rho att C r x b guard mf mc pc /\\
                      memaccess_inbounds e2
                       [sig,3309; sk,4032; word_sub fp (word 1472),14432;
                        word(pc + got_stack_chk_guard),8; guard,8;
                        word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                        word(pc + rodata_mld_KeccakF_RoundConstants),192;
                        word(pc + rodata_mld_zetas),1024;
                        word(pc + mldsa65_signature_internal_consts),336]
                       [sig,3309; word_sub fp (word 1472),14432]))
              (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [X18; X21; X22; X23; X24; X25; X27; X30] ,,
               MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
               MAYCHANGE [memory :> bytes(sig,3309);
                          memory :> bytes(word_sub fp (word 1472),1472);
                          memory :> bytes(word_add fp (word 76),4);
                          memory :> bytes(word_add fp (word 80),240);
                          memory :> bytes(word_add fp (word 384),16);
                          memory :> bytes(word_add fp (word 416),16);
                          memory :> bytes(word_add fp (word 544),1024);
                          memory :> bytes(word_add fp (word 1856),1024);
                          memory :> bytes(word_add fp (word 2880),1024);
                          memory :> bytes(word_add fp (word 3904),6144);
                          memory :> bytes(word_add fp (word 10048),768);
                          memory :> bytes(word_add fp (word 10816),1024);
                          memory :> bytes(word_add fp (word 11840),16);
                          memory :> bytes(word_add fp (word 11872),48);
                          memory :> bytes(word_add fp (word 11936),1000)])");;

let SI65_ATT_EXEC = MLDSA_NATIVE_SIGNATURE_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;

let SI65_ATT_ALLOWED =
  [`sig:int64`; `sk:int64`; `fp:int64`; `rho:num`; `att:num`; `C:num`; `r:num`;
   `x:num->int32`; `b:num->byte`; `guard:int64`; `mf:int64`; `mc:int64`; `pc:num`];;

let SI65_ATT_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc SI65_ATT_EXEC name
    ilist SI65_ATT_ALLOWED n;;

let SI65_ATT_MID = parse_term(
 "\\s. read SP s = fp /\\
      read X21 s = (if r = 18 then word 1 else word 0) /\\
      read X20 s = word_add fp (word 10816) /\\
      read (memory :> bytes32 (word_add fp (word 76))) s = word att /\\
      read (memory :> bytes64(word(pc + got_stack_chk_guard))) s = guard /\\
      read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
      read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
      read (memory :> bytes(ea,el)) s = ev /\\
      (r = 18
       ==> !t. t < 3309
               ==> read (memory :> bytes8 (word_add sig (word t))) s =
                   (" ^ string_of_term SI65_SIGATT ^ ") t)");;

let SI65_ATT_PC_TAC =
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read PC s = x`) (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NUM_LT_CONV THENC REWRITE_CONV[]) th else th) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `read PC s = x`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC;;

let SI65_PATH_END_TAC =
  SIGN_BETA_ALL_TAC THEN SIGN_SELECT_TAC THEN SIGN_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [SIGN_PATH_UNIFY_TAC; SI65_LOOP_MEMACCESS_TAC];;

let SI65_ATT_FIN_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN (SI65_MAYCHANGE_TAC ORELSE SI65_PATH_END_TAC);;

let SI65_ATT_TEMPLATE =
 `\(sig:int64) (sk:int64) (fp:int64) (rho:num) (att:num) (C:num) (r:num) (x:num->int32)
   (b:num->byte) (guard:int64) (mf:int64) (mc:int64) (pc:num).
   APPEND (f_ev_cl sig sk fp rho att C r x b guard mf mc pc)
    (APPEND
      (if r < 5 then f_ev_pz sig sk fp rho att C r x b guard mf mc pc
       else if r < 17
       then if EVEN (r - 5) then f_ev_pw1 sig sk fp rho att C r x b guard mf mc pc
            else f_ev_pw2 sig sk fp rho att C r x b guard mf mc pc
       else f_ev_pt sig sk fp rho att C r x b guard mf mc pc)
      (f_ev_hd sig sk fp rho att C r x b guard mf mc pc))
   :(uarch_event)list`;;

let SI65_ATT_SETUP_TAC =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,_ = CONJ_PAIR th in
    MAP_EVERY (fun (th,n) -> SI65_ASSUME_CALLEE_TAILED_TAC th n)
     [MP (SPEC_ALL SI65_HEAD) th,"H_HEAD"; MP (SPEC_ALL SI65_ZPRE) th,"H_ZPRE";
      MP (SPEC_ALL SI65_ZIT) th,"H_ZIT"; SI65_RPRE,"H_RPRE"; SI65_RIT,"H_RIT";
      SI65_TAIL,"H_TAIL"; MP (SPEC_ALL SI65_CLEAN) ms,"H_CLEAN"]) THEN
  CONCRETIZE_F_EVENTS_TAC SI65_ATT_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `sk:int64`; `skb:num->byte`; `fp:int64`;
    `rho:num`; `MU:num`; `RHO:num`; `att:num`; `C:num`; `r:num`; `x:num->int32`;
    `b:num->byte`; `guard:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst SI65_ATT_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SI65_ALIGNED16_32) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
   `mld_sign_attempt_declass k l ctlen tau g1 bndz bndw bndh w1enc w1p dlo
     mkhint omega A s1hat s2hat t0hat mu rhoprime kappa = (C,r,x,b)`)
   (concl th))) THEN
  REWRITE_TAC[mld_sign_attempt_declass] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[mld_sign_cphat; th]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV)) THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SIGN_REJ_CASES o check (fun th ->
    can (term_match []
     `mld_sign_rej k l bndz bndw bndh omega mkhint z r0 ct0 x w1 = r`)
     (concl th))) THEN
  CONV_TAC(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV)) THEN
  STRIP_TAC;;

let SI65_ATT_CPH_TAC =
  FIRST_ASSUM(fun cth ->
    if can (term_match [] `num_of_bytelist l = (C:num)`) (concl cth) &&
       rhs(concl cth) = `C:num` then
      RULE_ASSUM_TAC(fun th ->
        let c = concl th in
        if can (find_term (fun t -> is_const t && fst(dest_const t) = "ensures")) c then th
        else if can (find_term (fun t -> is_const t && fst(dest_const t) = "mld_sign_cphat")) c
        then REWRITE_RULE[cth] (REWRITE_RULE[mld_sign_cphat] th) else th)
    else NO_TAC);;

(*** z_r fails, r < 5 ***)

let SI65_ATT_ZCASE_TAC =
  SUBGOAL_THEN `r <= 5 /\ ~(r = 18)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `r < 5` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `r < 5 ==> P`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SI65_ATT_CALL_TAC "H_ZPRE"
   [`r:num`; `sig:int64`; `sk:int64`; `skb:num->byte`; `fp:int64`; SI65_ATT_CPH;
    `RHO:num`; `att:num`; `pc:num`] 2 THEN
  SI65_ATT_PC_TAC THEN
  SI65_ATT_CALL_TAC "H_ZIT"
   [`F`; `sig:int64`; `sk:int64`; `skb:num->byte`; `fp:int64`; `r:num`; SI65_ATT_CPH;
    `RHO:num`; `att:num`; `pc:num`] 3 THEN
  SI65_ATT_PC_TAC THEN
  ARM_STEPS_TAC SI65_ATT_EXEC (4--6) THEN
  SI65_ATT_FIN_TAC;;

(*** check r - 5 of the rows fails, 5 <= r < 17 ***)

let SI65_ATT_WCASE_TAC =
  SUBGOAL_THEN `(r - 5) DIV 2 <= 6 /\ (r - 5) DIV 2 < 6 /\ ~(r = 18) /\
                2 * (r - 5) DIV 2 <= r - 5`
   STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `r < 17` THEN UNDISCH_TAC `5 <= r` THEN
    SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [SI65_ATT_R0; SI65_ATT_CT0; `261692`; `261888`; `r - 5`;
                `(r - 5) DIV 2`] SIGN_ROWS_GOOD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `j:num` o REWRITE_RULE[ASSUME `5 <= r`] o
      check (fun th -> can (term_match []
        `5 <= r ==> (!j. j < r - 5 /\ j < 12 ==> P j)`) (concl th))) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `j < r - 5` THEN UNDISCH_TAC `r < 17` THEN ARITH_TAC;
    DISCH_TAC] THEN
  SI65_ATT_CALL_TAC "H_ZPRE"
   [`5`; `sig:int64`; `sk:int64`; `skb:num->byte`; `fp:int64`; SI65_ATT_CPH;
    `RHO:num`; `att:num`; `pc:num`] 2 THEN
  SI65_ATT_PC_TAC THEN
  SI65_ATT_CALL_TAC "H_RPRE"
   [`(r - 5) DIV 2`; `sk:int64`; `skb:num->byte`; `fp:int64`; SI65_ATT_W; SI65_ATT_CPH;
    `pc:num`] 3 THEN
  SI65_ATT_PC_TAC THEN
  MP_TAC(SPECL [`fp:int64`; `3904`; `1536`; `mld_poly_decompose_lo_32`; SI65_ATT_W;
                `(r - 5) DIV 2`; `s3:armstate`] SIGN_ROW_SLICE) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [`s3:armstate`]
             `!k. 256 * ((r - 5) DIV 2) <= k /\ k < 1536
                  ==> read (memory :> bytes32 (word_add fp (word (3904 + 4 * k)))) s3 = Q k`)
           (concl th)
    then REWRITE_TAC[th] else NO_TAC) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `5 <= r /\ r < 17 ==> ~(P = word 0:int32)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `EVEN(r - 5)` THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `~(mld_poly_chknorm (if EVEN(r - 5) then a else b) (word w) = word 0)`)
      (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SI65_ATT_CALL_TAC "H_RIT"
     [`F`; `F`; `sk:int64`; `skb:num->byte`; `fp:int64`; `(r - 5) DIV 2`; SI65_ATT_W;
      SI65_ATT_CPH; `pc:num`] 4;
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `~(mld_poly_chknorm (if EVEN(r - 5) then a else b) (word w) = word 0)`)
      (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
     (SPECL [`5`; `r:num`] SIGN_ODD_ROW)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `r - 6` o REWRITE_RULE[ASSUME `5 <= r`] o
      check (fun th -> can (term_match []
        `5 <= r ==> (!j. j < r - 5 /\ j < 12 ==> P j)`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [UNDISCH_TAC `r < 17` THEN ARITH_TAC; DISCH_TAC] THEN
    SI65_ATT_CALL_TAC "H_RIT"
     [`T`; `F`; `sk:int64`; `skb:num->byte`; `fp:int64`; `(r - 5) DIV 2`; SI65_ATT_W;
      SI65_ATT_CPH; `pc:num`] 4] THEN
  SI65_ATT_PC_TAC THEN
  ARM_STEPS_TAC SI65_ATT_EXEC (5--7) THEN
  SI65_ATT_FIN_TAC;;

(*** the hints, r = 17 (too many) or 18 (success), both through TAIL ***)

let SI65_ATT_FACT_RW_TAC th =
  RULE_ASSUM_TAC(fun th' ->
    if can (find_term (fun t -> is_const t && fst(dest_const t) = "ensures")) (concl th') ||
       concl th' = concl th
    then th' else REWRITE_RULE[th] th');;

let SI65_ATT_TCASE_TAC =
  SUBGOAL_THEN `17 <= r /\ 5 <= 5` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(r < 17)` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [SI65_ATT_R0; SI65_ATT_CT0; `261692`; `261888`; `12`; `6`] SIGN_ROWS_GOOD) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[LE_REFL] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `j:num` o REWRITE_RULE[ASSUME `5 <= r`] o
      check (fun th -> can (term_match []
        `5 <= r ==> (!j. j < r - 5 /\ j < 12 ==> P j)`) (concl th))) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `17 <= r` THEN UNDISCH_TAC `j < 12` THEN ARITH_TAC;
    DISCH_TAC] THEN
  SI65_ATT_CALL_TAC "H_ZPRE"
   [`5`; `sig:int64`; `sk:int64`; `skb:num->byte`; `fp:int64`; SI65_ATT_CPH;
    `RHO:num`; `att:num`; `pc:num`] 2 THEN
  SI65_ATT_PC_TAC THEN
  SI65_ATT_CALL_TAC "H_RPRE"
   [`6`; `sk:int64`; `skb:num->byte`; `fp:int64`; SI65_ATT_W; SI65_ATT_CPH; `pc:num`] 3 THEN
  SI65_ATT_PC_TAC THEN
  SI65_ASM_RW_TAC[ARITH_RULE `256 * 6 = 1536`; ARITH_RULE `0 < 6`; ARITH_RULE `0 < 5`] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `(if 17 <= r then p else q) = (x:num->int32)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
    SI65_ATT_FACT_RW_TAC th THEN ASSUME_TAC th) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `(if 17 <= r then p else q) = (b:num->byte)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!j. j < 768
        ==> read (memory :> bytes8 (word_add fp (word (10048 + j)))) s3 =
            (b:num->byte) j`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(fun th ->
      if is_var(rhs(concl th)) && name_of(rhs(concl th)) = "b"
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[mld_sign_hint_w1] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SI65_ATT_CALL_TAC "H_TAIL"
   [`sig:int64`; `fp:int64`; `C:num`; `x:num->int32`; `b:num->byte`; `pc:num`] 4 THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `17 <= r ==> (r = 18 <=> P)`) (concl th))) THEN
  ASM_REWRITE_TAC[NOT_LT] THEN DISCH_TAC THEN
  ASM_CASES_TAC `r = 18` THENL
   [SUBGOAL_THEN `mld_hint_count (mld_polyvec_make_hint_32 x b) 1536 <= 55` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if is_iff(concl th) && lhs(concl th) = `r = 18`
                            then ACCEPT_TAC(EQ_MP th (ASSUME `r = 18`)) else NO_TAC); ALL_TAC] THEN
    SI65_ATT_FACT_RW_TAC
      (ASSUME `mld_hint_count (mld_polyvec_make_hint_32 x b) 1536 <= 55`) THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [`sig:int64`; `C:num`] `read (memory :> bytes (sig,48)) s = C`)
             (concl th)
      then FIRST_ASSUM(fun cth ->
             if is_var(rhs(concl cth)) && name_of(rhs(concl cth)) = "C" &&
                can (term_match [] `num_of_bytelist l = (C:num)`) (concl cth)
             then ASSUME_TAC(MATCH_MP SIGN_BYTES8_OF_READ_BYTES (TRANS th (SYM cth)))
             else NO_TAC)
      else NO_TAC) THEN
    REPEAT(FIRST_X_ASSUM(fun th -> if concl th = `r = 18` then ASSUME_TAC(EQT_INTRO th)
                                   else NO_TAC)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(REWRITE_TAC[mld_sign_attempt_sig] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[mld_sign_cphat] THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `3309 = (48 + 5 * 640) + 61` SUBST1_TAC THENL
       [ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC SIGN_SIG_ASSEMBLE THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(ACCEPT_TAC o CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
        check (fun th -> can (term_match []
          `!t. t < 640 * 5
               ==> read (memory :> bytes8 (word_add sig (word (48 + t)))) s =
                   P t`) (concl th))) THEN NO_TAC) THEN
    (SI65_MAYCHANGE_TAC ORELSE SI65_PATH_END_TAC);
    SUBGOAL_THEN `~(mld_hint_count (mld_polyvec_make_hint_32 x b) 1536 <= 55)` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if is_iff(concl th) && lhs(concl th) = `r = 18`
                            then MP_TAC th else NO_TAC) THEN
      REWRITE_TAC[ASSUME `~(r = 18)`]; ALL_TAC] THEN
    SI65_ATT_FACT_RW_TAC
      (ASSUME `~(mld_hint_count (mld_polyvec_make_hint_32 x b) 1536 <= 55)`) THEN
    SI65_ATT_FIN_TAC];;

let SI65_ATT_PATHS_TAC =
  ASM_CASES_TAC `r < 5` THENL
   [SI65_ATT_ZCASE_TAC;
    SUBGOAL_THEN `5 <= r /\ 5 <= 5` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~(r < 5)` THEN ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `5 <= r ==> (!i. i < 5 ==> P i)`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_CASES_TAC `r < 17` THENL [SI65_ATT_WCASE_TAC; SI65_ATT_TCASE_TAC]];;

let SI65_ATT_CLEAN_TAC =
  FULL_INIT_TAC THEN
  SI65_ATT_CALL_TAC "H_CLEAN" [`r = 18`; `att:num`; `fp:int64`; `pc:num`] 1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  (SI65_MAYCHANGE_TAC ORELSE
   (SAFE_META_EXISTS_TAC allowed_vars_e THEN
    CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
    CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; SI65_LOOP_MEMACCESS_TAC]));;

let SI65_ATT = prove
 (SI65_ATT_STMT,
  SI65_ATT_SETUP_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa65_signature_internal_join12` SI65_ATT_MID THEN
  CONJ_TAC THENL
   [FULL_INIT_TAC THEN
    SI65_ATT_CALL_TAC "H_HEAD"
     [`fp:int64`; `att:num`; `rho:num`; `RHO:num`; `MU:num`; `C:num`; `guard:int64`;
      `pc:num`] 1 THEN
    SI65_ATT_CPH_TAC THEN SI65_ATT_PATHS_TAC;
    SI65_ATT_CLEAN_TAC]);;
