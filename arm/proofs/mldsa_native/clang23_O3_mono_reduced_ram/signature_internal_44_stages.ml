(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The stages of an attempt of mldsa44_signature_internal (clang 23 -O3 mono *)
(* reduced-RAM), as FULL lemmas for segments of the code, following the      *)
(* parts of the gcc reduced-RAM proof                                        *)
(* (gcc12_O2_reduced_ram/signature_internal_44_proof.ml) and of the x86      *)
(* proof of the same build, with the region lemmas of                        *)
(* signature_internal_44_inline.ml for the inlined code. fp is the stack     *)
(* pointer after the prologue (aligned to 32); the callees use at most 1472  *)
(* bytes below it, so the frame of the stages is fp - 1472 .. fp + 11200.    *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/signature_internal_44_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/signature_internal_44_inline.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_ntt_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/utils/mldsa_native_signing.ml";;
needs "arm/proofs/utils/mldsa_native_lazy_matrix.ml";;

let SI44_EXEC_RANGE lo hi =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   ([(layout ("mldsa44_signature_internal_" ^ lo),
      layout ("mldsa44_signature_internal_" ^ hi))] @
    [layout_range "plt_memcpy"; layout_range "plt_memset"]);;

(*** fp as fb_si + d in the goal and the assumptions, so that the memory    ***)
(*** safety checks compare regions with one base and no offsets that wrap  ***)
(*** (SI_FB_NORM_TAC of x86's inline_sign_stage.ml, with fp for rsp0)       ***)

let SI_FB_NORM_TAC d =
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

(*** The events at the end of a stage: the existential, the unification of ***)
(*** the template and the memory safety, with fp normalized               ***)

let SI44_SAFETY_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  (CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]) THEN
  SI_FB_NORM_TAC 1472 THEN
  REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN
  REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

(*** ASSUME_CALLEE_SAFETY_TAILED_TAC for a stage lemma with many variables: ***)
(*** the same assumption, with the quantifiers rotated by a derived rule   ***)
(*** rather than by MESON, which gives up ("Too deep") beyond about ten    ***)
(*** variables (SI_ASSUME_CALLEE_TAILED_TAC of x86's inline_sign_stage.ml). ***)

let SI_ASSUME_CALLEE_TAILED_TAC =
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

let SI44_GOT_TAC =
  W(fun (asl,w) ->
    MAP_EVERY (fun (_,th) ->
      let c = concl th in
      if is_eq c &&
         can (term_match [] `read (memory :> bytes64 (word (pc + n))) s`) (lhs c)
      then ASSUME_TAC(REWRITE_RULE[WORD_ADD] th) else ALL_TAC) asl);;

(*** A call of memset through the PLT, the BL being step n ***)

let SI44_MEMSET_TAC exec allowed n =
  LIBC_PLT_TAC exec n THEN
  G1_LIBC_CALL_TAC "H_MEMSET" exec
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`]
   allowed (n + 5);;

(* ------------------------------------------------------------------------- *)
(* The cleanup of an attempt (CLEAN), from join11 with x19 = 1 on success    *)
(* and 0 otherwise: the memsets of z (fp + 2144), c (fp + 3168), w (fp +     *)
(* 4192), w1 packed (fp + 8288) and the scratch polynomial (fp + 9056), the  *)
(* zeroing of the structure of rho'' (fp + 10080) and of c~ (fp + 10112),    *)
(* and the test of w19: to loop2_exit2 on success, else to the next attempt  *)
(* (loop2, with the count att + 1 in w9) or, after the last, to              *)
(* loop2_exit1.                                                              *)
(* ------------------------------------------------------------------------- *)

let SI44_CLEAN_STMT =
 `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e ok att fp pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 fp /\ att < 16382 /\
          ALL (nonoverlapping (word_sub fp (word 1472),12672))
              [(word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa44_signature_internal_join11) /\
                    read SP s = fp /\
                    read X19 s = (if ok then word 1 else word 0) /\
                    read (memory :> bytes32 (word_add fp (word 204))) s = word att /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read events s = e)
               (\s. read PC s =
                    (if ok then word (pc + mldsa44_signature_internal_loop2_exit2)
                     else if att + 1 < 16382
                     then word (pc + mldsa44_signature_internal_loop2)
                     else word (pc + mldsa44_signature_internal_loop2_exit1)) /\
                    read SP s = fp /\
                    (~ok ==> read X9 s = word (att + 1)) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (exists e2. read events s = APPEND e2 e /\
                       e2 = f_events ok att fp mf pc /\
                       memaccess_inbounds e2
                        [word_sub fp (word 1472),12672; word(pc + got_memset),8; ea,el]
                        [word_sub fp (word 1472),12672]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
                MAYCHANGE [memory :> bytes(word_add fp (word 2144),1024);
                           memory :> bytes(word_add fp (word 3168),1024);
                           memory :> bytes(word_add fp (word 4192),4096);
                           memory :> bytes(word_add fp (word 8288),768);
                           memory :> bytes(word_add fp (word 9056),1024);
                           memory :> bytes(word_add fp (word 10080),16);
                           memory :> bytes(word_add fp (word 10112),32)])`;;

let SI44_CLEAN_EXEC = SI44_EXEC_RANGE "join11" "loop2_exit1";;

(*** The test of the count of the attempts (cmp w8, #16380; b.ls) and the ***)
(*** next count                                                           ***)

let SI44_ATT_TEST = prove
 (`!att. att < 16382
         ==> (~(&(val (word att:int32)) - &16380:int =
                &(val (word_sub (word att:int32) (word 16380))) /\
                ~(val (word_sub (word att:int32) (word 16380)) = 0)) <=>
              att + 1 < 16382)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`word att:int32`; `16380`] GLUE_FLAGS_LS) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `att MOD 4294967296 = att` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let SI44_ATT_INC = prove
 (`!att. att < 16382
         ==> word_zx (word_add (word att:int32) (word 1)):int64 = word (att + 1)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD; DIMINDEX_32;
              DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `att MOD 4294967296 = att /\ (att + 1) MOD 4294967296 = att + 1 /\
                (att + 1) MOD 18446744073709551616 = att + 1` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_REWRITE_TAC[]]);;

(*** Split on a boolean p, rewriting the other assumptions with it ***)

let SI44_CASES_TAC p =
  ASM_CASES_TAC p THEN
  FIRST_ASSUM(fun th -> if concl th = p || concl th = mk_neg p
    then RULE_ASSUM_TAC(fun th' -> if concl th' = concl th then th'
                                   else REWRITE_RULE[th] th')
    else NO_TAC);;

let SI44_CLEAN = prove
 (SI44_CLEAN_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[memset_full_contract] th) "H_MEMSET") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(ok:bool) (att:num) (fp:int64) (mf:int64) (pc:num).
      if ok then f_ev_ok fp mf pc
      else if att + 1 < 16382 then f_ev_nx fp mf pc
      else f_ev_ex fp mf pc:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `ok:bool`; `att:num`; `fp:int64`;
                       `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; fst SI44_CLEAN_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN SI44_GOT_TAC THEN
  (let ms = SI44_MEMSET_TAC SI44_CLEAN_EXEC [`fp:int64`; `mf:int64`; `pc:num`] in
   ARM_STEPS_TAC SI44_CLEAN_EXEC (1--4) THEN ms 4 THEN
   ARM_STEPS_TAC SI44_CLEAN_EXEC (10--14) THEN ms 14 THEN
   ARM_STEPS_TAC SI44_CLEAN_EXEC (20--25) THEN ms 25 THEN
   ARM_STEPS_TAC SI44_CLEAN_EXEC (31--35) THEN ms 35 THEN
   ARM_STEPS_TAC SI44_CLEAN_EXEC (41--45) THEN ms 45 THEN
   ARM_STEPS_TAC SI44_CLEAN_EXEC (51--60)) THEN
  SI44_CASES_TAC `ok:bool` THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV WORD_RED_CONV)) THEN ASM_REWRITE_TAC[] THENL
   [ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SI44_SAFETY_TAC;
    ALL_TAC] THEN
  ARM_STEPS_TAC SI44_CLEAN_EXEC (61--65) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `att:num` SI44_ATT_TEST) (ASSUME `att < 16382`);
    MP (SPEC `att:num` SI44_ATT_INC) (ASSUME `att < 16382`)]) THEN
  SI44_CASES_TAC `att + 1 < 16382` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SI44_SAFETY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The packing of c~ and of the hints (TAIL), from the exit of the loop over *)
(* the rows (loop35_exit1): c~ (32 bytes at fp + 10112) copied to sig, the   *)
(* 84 bytes of the hints zeroed, and for each row k the unpacking of its w1  *)
(* (SI44_W1U) and its hints (SI44_HROW), with the count of row k stored at   *)
(* sig + 2416 + k. If the hints fit, the code sets w19 to 1 and goes to the  *)
(* cleanup at join11 with the hints of mld_pack_hints at sig + 2336;         *)
(* otherwise it goes there through join9 with w19 = 0.                       *)
(* ------------------------------------------------------------------------- *)

let SI44_SLOT_FACTS l = String.concat "" (map (fun (a,v) ->
  Printf.sprintf
   "read (memory :> bytes64 (word_add fp (word %d))) s = word_add fp (word %d) /\\\n" a v) l);;

let SI44_TAIL_STMT = parse_term(
 "exists f_events.
    forall e sig fp (C:num) (x:num->int32) (b:num->byte) pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 16 fp /\\
      nonoverlapping (sig,2420) (word_sub fp (word 1472),12672) /\\
      ALL (nonoverlapping (word pc,libmldsa_size))
          [(sig,2420); (word_sub fp (word 1472),12672)]
      ==> ensures arm
           (\\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read PC s = word (pc + mldsa44_signature_internal_loop35_exit1) /\\
                read SP s = fp /\\
                read X23 s = word_add fp (word 9056) /\\
                read X14 s = word_add (word pc) (word 245760) /\\
                read X16 s = word_add (word pc) (word 245760) /\\
                read (memory :> bytes64 (word_add fp (word 192))) s = sig /\\
                read (memory :> bytes64 (word_add fp (word 48))) s =
                word_add sig (word 2336) /\\\n" ^
  SI44_SLOT_FACTS [24,7264; 32,6240; 40,5216; 168,8864; 176,8672; 184,8480] ^
 "              read (memory :> bytes128 (word_add fp (word 288))) s =
                word 0xffffff07ffffff06ffffff05ffffff04 /\\
                read (memory :> bytes128 (word_add fp (word 304))) s =
                word 0xffffff03ffffff02ffffff01ffffff00 /\\
                read (memory :> bytes (word_add fp (word 10112),32)) s = C /\\
                (!j. j < 1024 ==> read (memory :> bytes32 (word_add fp (word (4192 + 4 * j)))) s = x j) /\\
                (!j. j < 768 ==> read (memory :> bytes8 (word_add fp (word (8288 + j)))) s = b j) /\\
                read events s = e)
           (\\s. read PC s = word (pc + mldsa44_signature_internal_join11) /\\
                read SP s = fp /\\
                read X19 s =
                (if mld_hint_count (mld_polyvec_make_hint_88 x b) 1024 <= 80
                 then word 1 else word 0) /\\
                read (memory :> bytes (sig,32)) s = C /\\
                (mld_hint_count (mld_polyvec_make_hint_88 x b) 1024 <= 80
                 ==> !t. t < 84
                         ==> read (memory :> bytes8 (word_add sig (word (2336 + t)))) s =
                             mld_pack_hints 80 4 (mld_polyvec_make_hint_88 x b) t) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events sig fp pc x b /\\
                   memaccess_inbounds e2
                    [sig,2420; word_sub fp (word 1472),12672;
                     word(pc + mldsa44_signature_internal_consts),128]
                    [sig,2420; word_sub fp (word 1472),12672]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
            MAYCHANGE [X19; X20; X21; X27] ,,
            MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
            MAYCHANGE [memory :> bytes(sig,32);
                       memory :> bytes(word_add sig (word 2336),84);
                       memory :> bytes(word_add fp (word 9056),1024)])");;

let SI44_TAIL_EXEC = SI44_EXEC_RANGE "loop35_exit1" "loop2_exit2";;

(*** The bytes of a zero region (SIGN_BYTES8_ZERO of x86's utils) ***)

let SI44_BYTES8_ZERO = prove
 (`!(a:int64) n (s:armstate).
        read (memory :> bytes(a,n)) s = 0
        ==> !t. t < n
                ==> read (memory :> bytes8 (word_add a (word t))) s = word 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `n:num`; `0`; `t:num`; `1`; `s:armstate`]
    READ_MEMORY_BYTES_SUB) THEN
  ASM_REWRITE_TAC[DIV_0; MOD_0] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0; BYTES8_WBYTES; READ_COMPONENT_COMPOSE;
              VAL_READ_WBYTES; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[GSYM READ_COMPONENT_COMPOSE]);;

let SI44_TL_TEMPLATE =
 `\(sig:int64) (fp:int64) (pc:num) (x:num->int32) (b:num->byte).
   if mld_hint_count (mld_polyvec_make_hint_88 x b) 256 <= 80 then
    (if mld_hint_count (mld_polyvec_make_hint_88 x b) 512 <= 80 then
      (if mld_hint_count (mld_polyvec_make_hint_88 x b) 768 <= 80 then
        (if mld_hint_count (mld_polyvec_make_hint_88 x b) 1024 <= 80
         then f_ev_ok sig fp pc x b else f_ev_r3 sig fp pc x b)
       else f_ev_r2 sig fp pc x b)
     else f_ev_r1 sig fp pc x b)
   else f_ev_r0 sig fp pc x b :(uarch_event)list`;;

let SI44_TL_ALLOWED = [`sig:int64`; `fp:int64`; `pc:num`; `x:num->int32`; `b:num->byte`];;

let SI44_TL_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc SI44_TAIL_EXEC
    name ilist SI44_TL_ALLOWED n;;

(*** The facts for row k of b and of x at state n ***)

let SI44_TL_B_SLICE_TAC k n =
  let ib = 8288 + 192 * k and wb = 192 * k in
  let st = mk_var("s"^string_of_int n,`:armstate`) in
  SUBGOAL_THEN (vsubst [st,`s:armstate`] (parse_term(Printf.sprintf
    "!j. j < 192 ==> read (memory :> bytes8 (word_add fp (word (%d + j)))) s = b (%d + j)" ib wb)))
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC (parse_term(Printf.sprintf "%d + j" wb)) o check (fun th ->
      is_forall(concl th) && can (term_match []
       `!j. j < 768 ==> read (memory :> bytes8 (word_add fp (word (8288 + j)))) s = b j`)
       (concl th))) THEN
    REWRITE_TAC[ARITH_RULE(parse_term(Printf.sprintf "8288 + %d + j = %d + j" wb ib))] THEN
    DISCH_THEN MATCH_MP_TAC THEN UNDISCH_TAC `j < 192` THEN ARITH_TAC;
    ALL_TAC];;

let SI44_TL_X_SLICE_TAC k n =
  let w = 4192 + 1024 * k and p0 = 256 * k in
  let st = mk_var("s"^string_of_int n,`:armstate`) in
  SUBGOAL_THEN (vsubst [st,`s:armstate`] (parse_term(Printf.sprintf
    "!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (%d + 4 * i)))) s = x (%d + i)" w p0)))
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC (parse_term(Printf.sprintf "%d + i" p0)) o check (fun th ->
      is_forall(concl th) && can (term_match []
       `!j. j < 1024 ==> read (memory :> bytes32 (word_add fp (word (4192 + 4 * j)))) s = x j`)
       (concl th))) THEN
    REWRITE_TAC[ARITH_RULE(parse_term(Printf.sprintf "4192 + 4 * (%d + i) = %d + 4 * i" p0 w))] THEN
    DISCH_THEN MATCH_MP_TAC THEN UNDISCH_TAC `i < 256` THEN ARITH_TAC;
    ALL_TAC];;

let SI44_TL_CNT_TM p = subst [mk_small_numeral p,`p:num`]
  `mld_hint_count (mld_polyvec_make_hint_88 x b) p <= 80`;;

let SI44_TL_SPLIT_TAC p =
  let c = SI44_TL_CNT_TM p in
  ASM_CASES_TAC c THEN
  FIRST_ASSUM(fun th -> if concl th = c || concl th = mk_neg c
    then RULE_ASSUM_TAC(fun th' -> if concl th' = concl th then th' else REWRITE_RULE[th] th')
    else NO_TAC) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && free_in `X8` (concl th)
                                then STRIP_ASSUME_TAC th else NO_TAC));;

(*** A hint that does not fit: through join9 (4 instructions from step n) ***)

let SI44_TL_FAIL_TAC p n =
  SUBGOAL_THEN (mk_neg(SI44_TL_CNT_TM 1024)) ASSUME_TAC THENL
   [MP_TAC(SPECL [`mld_polyvec_make_hint_88 x b`; mk_small_numeral p; `1024`]
                 MLD_HINT_COUNT_MONO) THEN
    FIRST_ASSUM(MP_TAC o check (fun th -> concl th = mk_neg(SI44_TL_CNT_TM p))) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ARM_STEPS_TAC SI44_TAIL_EXEC (n--(n+3)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SI44_SAFETY_TAC;;

let SI44_ZX_BYTE = prove
 (`!n. word_zx (word_zx (word n:int64):int32):byte = word n`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_32;
              DIMINDEX_64] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

let SI44_TL_PACK_TAC =
  X_GEN_TAC `t:num` THEN DISCH_TAC THEN REWRITE_TAC[mld_pack_hints] THEN
  CONV_TAC NUM_REDUCE_CONV THEN COND_CASES_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    SUBGOAL_THEN `t = 80 \/ t = 81 \/ t = 82 \/ t = 83` MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`t < 84`; `~(t < 80)`] THEN ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[SI44_ZX_BYTE]];;

let SI44_TL_COUNT0_TAC =
  ASSUME_TAC(INST [`mld_polyvec_make_hint_88 x b`,`h:num->bool`]
                  (CONJUNCT1 mld_hint_count)) THEN
  ASSUME_TAC(ARITH_RULE `0 <= 80`);;

(*** Rows 1 to 3 from step n (the HROW of the row before): the glue up to ***)
(*** the w1 unpack loop (8 instructions), the loop, g2 instructions up to ***)
(*** the hint loop and the loop, then the split on the count              ***)

let SI44_TL_ROW_TAC k n g2 =
  let p1 = 256 * (k + 1) in
  let nw = n + 9 in let nh = nw + g2 + 1 in
  ARM_STEPS_TAC SI44_TAIL_EXEC ((n+1)--(n+8)) THEN SI44_TL_B_SLICE_TAC k (n+8) THEN
  SI44_TL_CALL_TAC ("H_W1U"^string_of_int k)
   [`word_add fp (word 9056):int64`;
    parse_term(Printf.sprintf "word_add fp (word %d):int64" (8288 + 192 * k));
    parse_term(Printf.sprintf "\\t. (b:num->byte) (%d + t)" (192 * k)); `pc:num`] nw THEN
  ARM_STEPS_TAC SI44_TAIL_EXEC ((nw+1)--(nh-1)) THEN SI44_TL_X_SLICE_TAC k (nh-1) THEN
  SI44_TL_CALL_TAC ("H_HROW"^string_of_int k)
   [`x:num->int32`; `b:num->byte`; `sig:int64`; `fp:int64`; `pc:num`] nh THEN
  SI44_TL_SPLIT_TAC p1 THENL [ALL_TAC; SI44_TL_FAIL_TAC p1 (nh+1)];;

let SI44_TAIL = prove
 (SI44_TAIL_STMT,
  MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
   (zip SI44_W1U ["H_W1U0"; "H_W1U1"; "H_W1U2"; "H_W1U3"] @
    zip SI44_HROW ["H_HROW0"; "H_HROW1"; "H_HROW2"; "H_HROW3"]) THEN
  CONCRETIZE_F_EVENTS_TAC SI44_TL_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `sig:int64`; `fp:int64`; `C:num`;
                       `x:num->int32`; `b:num->byte`; `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; fst SI44_TAIL_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN
  MAP_EVERY (fun n ->
    MP_TAC(SPECL [`word_add fp (word 10112):int64`; `32`; `C:num`; mk_small_numeral n;
                  `s0:armstate`] SIGN_BYTES128_OF_BYTES) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC) [0;1] THEN
  ARM_STEPS_TAC SI44_TAIL_EXEC (1--20) THEN
  (*** sig[0,32) = C and the zero hint bytes ***)
  SUBGOAL_THEN `C < 2 EXP (8 * 32)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if can (term_match []
       `read (memory :> bytes (word_add fp (word 10112),32)) s0 = C`) (concl th)
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[READ_BYTES_BOUND; READ_COMPONENT_COMPOSE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`sig:int64`; `C:num`; `2`; `s20:armstate`] SIGN_BYTES_OF_BYTES128) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0; DIV_1] THEN ASM_REWRITE_TAC[DIV_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `C MOD 2 EXP (128 * 2) = C` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN
    FIRST_ASSUM(MP_TAC o check (fun th -> concl th = `C < 2 EXP (8 * 32)`)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`word_add sig (word 2336):int64`; `0`; `5`; `s20:armstate`]
               SIGN_BYTES_OF_BYTES128) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MOD_0] THEN CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  DISCH_THEN(fun th -> ASSUME_TAC(GEN `t:num`
    (REWRITE_RULE[GSYM(INST [`mld_polyvec_make_hint_88 x b`,`h:num->bool`]
                             (CONJUNCT1 mld_hint_index));
                  WORD_RULE `word_add (word_add sig (word 2336)) (word t) =
                             word_add sig (word (2336 + t))`]
      (SPEC `t:num` (MATCH_MP SI44_BYTES8_ZERO th))))) THEN
  (*** row 0 ***)
  SI44_TL_B_SLICE_TAC 0 20 THEN
  SI44_TL_CALL_TAC "H_W1U0"
   [`word_add fp (word 9056):int64`; `word_add fp (word 8288):int64`;
    `\t. (b:num->byte) (0 + t)`; `pc:num`] 21 THEN
  ARM_STEPS_TAC SI44_TAIL_EXEC (22--28) THEN SI44_TL_X_SLICE_TAC 0 28 THEN
  SI44_TL_COUNT0_TAC THEN
  SI44_TL_CALL_TAC "H_HROW0"
   [`x:num->int32`; `b:num->byte`; `sig:int64`; `fp:int64`; `pc:num`] 29 THEN
  SI44_TL_SPLIT_TAC 256 THENL [ALL_TAC; SI44_TL_FAIL_TAC 256 30] THEN
  (*** rows 1 to 3, and the success ***)
  SI44_TL_ROW_TAC 1 29 5 THEN SI44_TL_ROW_TAC 2 44 2 THEN SI44_TL_ROW_TAC 3 56 2 THEN
  ARM_STEPS_TAC SI44_TAIL_EXEC (69--74) THEN ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [SI44_TL_PACK_TAC; SI44_SAFETY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* s2 and t0 in the NTT domain, from the secret key skb, as the row          *)
(* iterations unpack and transform them, polynomial by polynomial (as in the *)
(* gcc proof, SIGN44_S2H and SIGN44_T0H).                                    *)
(* ------------------------------------------------------------------------- *)

let SI44_S2U =
 `mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte)(512 + j))`;;
let SI44_S2H = mk_comb(`mld_polyvec_map mld_poly_ntt`,SI44_S2U);;
let SI44_T0U =
 `mld_polyvec_unpack 416 mld_polyt0_unpack (\j. (skb:num->byte)(896 + j))`;;
let SI44_T0H = mk_comb(`mld_polyvec_map mld_poly_ntt`,SI44_T0U);;

(* ------------------------------------------------------------------------- *)
(* One iteration of the loop over the rows of w0 (RIT), from loop35 with row *)
(* j in x21 and its address in x27: s2_j unpacked into the scratch          *)
(* polynomial at fp + 9056 and transformed, its product with the challenge,  *)
(* w0_j - c s2_j in place and reduced, its norm check; then t0_j likewise,   *)
(* c t0_j reduced and checked, and the sum in place in row j. ok1 and ok2    *)
(* are the results of the two checks (ok2 matters only when ok1 holds): if   *)
(* both pass, the code goes back to loop35 or, after the last row, to        *)
(* loop35_exit1, else to the rejection at join10. The callees (NTT, inverse  *)
(* NTT) use the stack below fp.                                              *)
(* ------------------------------------------------------------------------- *)

let SI44_RIT_R0 = list_mk_comb(`mld_sign_r0`,
  [`mld_poly_decompose_lo_88`; `w:num->int32`; SI44_S2H; `cphat:num->int32`; `j:num`]);;
let SI44_RIT_CT0 = list_mk_comb(`mld_sign_ct0`, [SI44_T0H; `cphat:num->int32`; `j:num`]);;

let SI44_PC245760 = String.concat "" (map (fun r ->
  "read " ^ r ^ " s = word_add (word pc) (word 245760) /\\\n")
  ["X14";"X15";"X16";"X17";"X18";"X0"]);;

let SI44_RIT_PRE =
 "read SP s = fp /\\
  read X23 s = word_add fp (word 9056) /\\ read X24 s = word 2 /\\
  read X25 s = word 18446744073701171199 /\\ read X28 s = word 252236767799803904 /\\
  read (memory :> bytes64 (word_add fp (word 208))) s = word_add fp (word 3176) /\\
  read (memory :> bytes64 (word_add fp (word 736))) s = word_add sk (word 512) /\\
  read (memory :> bytes64 (word_add fp (word 768))) s = word_add sk (word 896) /\\
  read (memory :> bytes128 (word_add fp (word 240))) s =
  word 339618401959998730991157055895298383871 /\\
  read (memory :> bytes128 (word_add fp (word 288))) s =
  word 0xffffff07ffffff06ffffff05ffffff04 /\\
  read (memory :> bytes128 (word_add fp (word 304))) s =
  word 0xffffff03ffffff02ffffff01ffffff00 /\\
  (!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (3168 + 4 * i)))) s =
                   cphat i) /\\
  (!i. i < 2560 ==> read (memory :> bytes8 (word_add sk (word i))) s = skb i)";;

let SI44_RIT_STMT = parse_term(
 "exists f_events.
    forall e ok1 ok2 sk skb fp j w cphat pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 16 fp /\\ j < 4 /\\
      (ok1 <=> mld_poly_chknorm (" ^ string_of_term SI44_RIT_R0 ^ ") (word 95154) = word 0) /\\
      (ok1 ==> (ok2 <=> mld_poly_chknorm (" ^ string_of_term SI44_RIT_CT0 ^ ") (word 95232) =
                        word 0)) /\\
      ALL (nonoverlapping (word_sub fp (word 1472),12672))
          [(sk,2560); (word pc,libmldsa_size)]
      ==> ensures arm
           (\\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read PC s = word (pc + mldsa44_signature_internal_loop35) /\\
                read X21 s = word j /\\ read X20 s = word (96 * j) /\\
                read X27 s = word_add fp (word (4192 + 1024 * j)) /\\\n" ^ SI44_PC245760 ^
 "              read (memory :> bytes64 (word_add fp (word 216))) s = word (6 + 416 * j) /\\
                read (memory :> bytes64 (word_add fp (word 224))) s =
                word_add fp (word (4208 + 1024 * j)) /\\\n" ^ SI44_RIT_PRE ^ " /\\
                (!i. i < 256 ==> read (memory :> bytes32
                                   (word_add fp (word ((4192 + 1024 * j) + 4 * i)))) s =
                                 mld_poly_decompose_lo_88 (mld_poly_of w j) i) /\\
                read events s = e)
           (\\s. read PC s =
                (if ok1 /\\ ok2
                 then (if j + 1 < 4 then word (pc + mldsa44_signature_internal_loop35)
                       else word (pc + mldsa44_signature_internal_loop35_exit1))
                 else word (pc + mldsa44_signature_internal_join10)) /\\
                read SP s = fp /\\
                (ok1 /\\ ok2
                 ==> read X21 s = word (j + 1) /\\ read X20 s = word (96 * (j + 1)) /\\
                     read X27 s = word_add fp (word (4192 + 1024 * (j + 1))) /\\\n" ^
  SI44_PC245760 ^
 "                   read (memory :> bytes64 (word_add fp (word 216))) s =
                     word (6 + 416 * (j + 1)) /\\
                     read (memory :> bytes64 (word_add fp (word 224))) s =
                     word_add fp (word (4208 + 1024 * (j + 1))) /\\
                     (!i. i < 256 ==> read (memory :> bytes32
                                        (word_add fp (word ((4192 + 1024 * j) + 4 * i)))) s =
                                      mld_poly_add (" ^ string_of_term SI44_RIT_R0 ^ ")
                                                   (" ^ string_of_term SI44_RIT_CT0 ^ ") i)) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events ok1 ok2 sk fp j pc /\\
                   memaccess_inbounds e2
                    [sk,2560; word_sub fp (word 1472),12672;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa44_signature_internal_consts),128]
                    [word_sub fp (word 1472),12672]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [X18; X19; X20; X21; X27; X30] ,,
            MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
            MAYCHANGE [memory :> bytes(word_sub fp (word 208),208);
                       memory :> bytes(word_add fp (word 216),16);
                       memory :> bytes(word_add fp (word 272),16);
                       memory :> bytes(word_add fp (word 320),416);
                       memory :> bytes(word_add fp (word (4192 + 1024 * j)),1024);
                       memory :> bytes(word_add fp (word 9056),1024)])");;

let SI44_RIT_EXEC = SI44_EXEC_RANGE "loop35" "loop35_exit1";;

let SI44_RIT_TEMPLATE =
 `\(ok1:bool) (ok2:bool) (sk:int64) (fp:int64) (j:num) (pc:num).
   if ok1 then
    (if ok2 then (if j + 1 < 4 then f_ev_mid sk fp j pc else f_ev_last sk fp j pc)
     else f_ev_f2 sk fp j pc)
   else f_ev_f1 sk fp j pc :(uarch_event)list`;;

let SI44_RIT_ALLOWED = [`ok1:bool`; `ok2:bool`; `sk:int64`; `fp:int64`; `j:num`; `pc:num`];;

let SI44_RIT_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc SI44_RIT_EXEC
    name ilist SI44_RIT_ALLOWED n;;

(*** Bytes off .. off + n - 1 of the secret key at state st ***)

let SI44_SK_SLICE_TAC off n st =
  let t = vsubst [st,`s:armstate`] (parse_term(Printf.sprintf
   "!k. k < %d ==> read (memory :> bytes8 (word_add sk (word (%s + k)))) s =
                   (skb:num->byte) (%s + k)" n off off)) in
  SUBGOAL_THEN t ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (term_match []
       `!i. i < 2560 ==> read (memory :> bytes8 (word_add sk (word i))) s = skb i`)
       (concl th))) THEN
    MAP_EVERY UNDISCH_TAC [`j < 4`; mk_binop `(<):num->num->bool` `k:num` (mk_small_numeral n)] THEN
    ARITH_TAC;
    ALL_TAC];;

(*** A register fact restated in the form a precondition needs (state n) ***)

let SI44_REG_FORM_TAC reg n (nw:term) =
  let s = mk_var("s"^string_of_int n,`:armstate`) in
  let lh = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                           mk_const(reg,[])),s) in
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = lh
    then let tm = mk_eq(rhs(concl th),nw) in
         let eth = try prove(tm, CONV_TAC(DEPTH_CONV WORD_RED_CONV))
                   with Failure _ -> WORD_RULE tm in
         ASSUME_TAC(TRANS th eth) else NO_TAC);;

(*** The checks as (P <=> ok), so that rewriting with them keeps ok1 and ok2, ***)
(*** and the branch on a check (cbnz w8) as ok                              ***)

let SI44_ORIENT_TAC =
  FIRST_X_ASSUM(fun th -> if is_iff(concl th) && lhs(concl th) = `ok1:bool`
                          then ASSUME_TAC(GSYM th) else NO_TAC) THEN
  FIRST_X_ASSUM(fun th -> if is_imp(concl th) && lhand(concl th) = `ok1:bool`
                          then ASSUME_TAC(CONV_RULE(RAND_CONV SYM_CONV) th) else NO_TAC);;

let SI44_DECIDE_TAC okv =
  FIRST_X_ASSUM(fun th ->
    if is_iff(concl th) && rhs(concl th) = okv then
      RULE_ASSUM_TAC(fun th' ->
        if can (term_match [] `read PC s = x`) (concl th') ||
           can (term_match [] `read events s = x`) (concl th')
        then REWRITE_RULE[th] (REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0] th')
        else th')
    else NO_TAC);;

(*** The end of a stage: the frame (callees below fp) and the events ***)

let SI44_MAYCHANGE_TAC =
  W(fun (asl,w) -> if maychange_term w then ALL_TAC else NO_TAC) THEN
  SI_FB_NORM_TAC 1472 THEN
  FIRST_X_ASSUM(fun th -> if maychange_term (concl th) && not(is_forall(concl th))
                          then MP_TAC th else NO_TAC) THEN
  DISCH_TAC THEN MONOTONE_MAYCHANGE_TAC;;

let SI44_END_TAC = REPEAT CONJ_TAC THEN (SI44_MAYCHANGE_TAC ORELSE SI44_SAFETY_TAC);;

let SI44_RIT_FAIL_TAC okv =
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read PC s = x`) (concl th)
                           then REWRITE_RULE[ASSUME(mk_neg okv)] th else th) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SI44_END_TAC;;

let SI44_RIT_POLY v = mk_comb(mk_comb(`mld_poly_of`,v),`j:num`);;
let SI44_RIT_PW1 = list_mk_comb(`mld_poly_pointwise_montgomery`,
  [SI44_RIT_POLY SI44_S2H; `cphat:num->int32`]);;
let SI44_RIT_PW2 = list_mk_comb(`mld_poly_pointwise_montgomery`,
  [SI44_RIT_POLY SI44_T0H; `cphat:num->int32`]);;
let SI44_RIT_CS2 = mk_comb(`mld_poly_invntt_tomont`,SI44_RIT_PW1);;
let SI44_RIT_W0J = `mld_poly_decompose_lo_88 (mld_poly_of (w:num->int32) j)`;;
let SI44_RIT_SUBX = list_mk_comb(`mld_poly_sub`,[SI44_RIT_W0J; SI44_RIT_CS2]);;

let SI44_RIT_LK l name =
  try assoc name l with Failure _ -> assoc ("mldsa44_signature_internal_" ^ name) l;;

let SI44_RIT_CALLEES () =
  [SI44_ETA_RTH,"H_ETA"; SI44_T0UNP,"H_T0U";
   MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_NTT";
   MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_INV";
   SI44_RIT_LK SI44_PWM "loop38","H_PWM38"; SI44_RIT_LK SI44_PWM "loop42","H_PWM42";
   SI44_RSUB,"H_RSUB"; SI44_RIT_LK SI44_RED "loop39","H_RED39";
   SI44_RIT_LK SI44_CHK "loop40","H_CHK40"; SI44_RIT_LK SI44_RED "loop43","H_RED43";
   SI44_RIT_LK SI44_CHK "loop44","H_CHK44"; SI44_RADD,"H_RADD"];;

(*** From loop35 to the first check (step 23) ***)

let SI44_RIT_PART1_TAC =
  SI44_SK_SLICE_TAC "512 + 96 * j" 96 `s0:armstate` THEN
  SI44_RIT_CALL_TAC "H_ETA" [`fp:int64`; `word_add sk (word 512):int64`; `j:num`;
    `\k. (skb:num->byte) (512 + 96 * j + k)`; `pc:num`] 1 THEN
  MLD_LAZY_REPOLY_TAC `mld_polyeta_unpack_2 (\k. (skb:num->byte) (512 + 96 * j + k))`
    (SI44_RIT_POLY SI44_S2U) [mld_polyvec_unpack; MLD_POLY_OF_POLYVEC] THEN
  ARM_STEPS_TAC SI44_RIT_EXEC (2--4) THEN
  SI44_RIT_CALL_TAC "H_NTT" [`read X0 s`; SI44_RIT_POLY SI44_S2U; `pc:num`;
                              `read SP s`; `read X30 s`] 5 THEN
  MLD_LAZY_REPOLY_TAC (mk_comb(`mld_poly_ntt`,SI44_RIT_POLY SI44_S2U))
    (SI44_RIT_POLY SI44_S2H) [MLD_POLY_OF_POLYVEC_MAP] THEN
  ARM_STEPS_TAC SI44_RIT_EXEC (6--8) THEN
  SI44_RIT_CALL_TAC "H_PWM38" [`word_add fp (word 9056):int64`;
    `word_add fp (word 3168):int64`; SI44_RIT_POLY SI44_S2H; `cphat:num->int32`;
    `pc:num`] 9 THEN
  ARM_STEPS_TAC SI44_RIT_EXEC (10--12) THEN
  SI44_RIT_CALL_TAC "H_INV" [`read X0 s`; SI44_RIT_PW1; `pc:num`; `read SP s`;
                              `read X30 s`] 13 THEN
  ARM_STEPS_TAC SI44_RIT_EXEC (14--15) THEN
  SI44_RIT_CALL_TAC "H_RSUB" [`fp:int64`; `word_add fp (word (4192 + 1024 * j)):int64`;
    SI44_RIT_W0J; SI44_RIT_CS2; `j:num`; `word_add fp (word (4208 + 1024 * j)):int64`;
    `pc:num`] 16 THEN
  SI44_REG_FORM_TAC "X8" 16 `word_add fp (word ((4192 + 1024 * j) + 16)):int64` THEN
  SI44_RIT_CALL_TAC "H_RED39" [`word_add fp (word (4192 + 1024 * j)):int64`;
    SI44_RIT_SUBX; `pc:num`] 17 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_r0]) THEN
  ARM_STEPS_TAC SI44_RIT_EXEC (18--21) THEN
  SI44_REG_FORM_TAC "X13" 21
    `word_zx (word_add (word_sub (word 95154:int32) (word 1)) (word 79)):int64` THEN
  SI44_REG_FORM_TAC "X8" 21 `word_zx (word 0:int32):int64` THEN
  SI44_RIT_CALL_TAC "H_CHK40" [`word_add fp (word (4192 + 1024 * j)):int64`;
    SI44_RIT_R0; `word 95154:int32`; `word 0:int32`; `pc:num`] 22 THEN
  ARM_STEPS_TAC SI44_RIT_EXEC [23] THEN
  SI44_DECIDE_TAC `ok1:bool` THEN SI44_CASES_TAC `ok1:bool` THENL
   [ALL_TAC; SI44_RIT_FAIL_TAC `ok1:bool`];;

(*** Bytes of the key with the address and the value offsets in their own ***)
(*** forms (aoff + k and voff + k, equal up to association)                ***)

let SI44_SK_SLICE2_TAC aoff voff n st =
  let t = vsubst [st,`s:armstate`] (parse_term(Printf.sprintf
   "!k. k < %d ==> read (memory :> bytes8 (word_add sk (word (%s + k)))) s =
                   (skb:num->byte) (%s + k)" n aoff voff)) in
  SUBGOAL_THEN t ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (term_match []
       `!i. i < 2560 ==> read (memory :> bytes8 (word_add sk (word i))) s = skb i`)
       (concl th))) THEN
    MAP_EVERY UNDISCH_TAC [`j < 4`; mk_binop `(<):num->num->bool` `k:num` (mk_small_numeral n)] THEN
    ARITH_TAC;
    ALL_TAC];;
(*** Steps that are ADRPs, each normalized ***)

let SI44_ADRP_STEPS_TAC exec ns =
  MAP_EVERY (fun n -> ARM_STEPS_TAC exec [n] THEN MLKEM_NATIVE_ADRP_TAC) ns;;
(*** From the first check to the second (step 56) ***)

let SI44_RIT_PART2_TAC =
  ARM_STEPS_TAC SI44_RIT_EXEC (24--27) THEN
  SI44_REG_FORM_TAC "X9" 27 `word_add sk (word ((896 + 416 * j) + 6)):int64` THEN
  SI44_SK_SLICE2_TAC "(896 + 416 * j)" "896 + 416 * j" 416 `s27:armstate` THEN
  SI44_RIT_CALL_TAC "H_T0U" [`word_add fp (word 9056):int64`;
    `word_add sk (word (896 + 416 * j)):int64`;
    `\k. (skb:num->byte) (896 + 416 * j + k)`; `pc:num`] 28 THEN
  MLD_LAZY_REPOLY_TAC `mld_polyt0_unpack (\k. (skb:num->byte) (896 + 416 * j + k))`
    (SI44_RIT_POLY SI44_T0U) [mld_polyvec_unpack; MLD_POLY_OF_POLYVEC] THEN
  ARM_STEPS_TAC SI44_RIT_EXEC (29--31) THEN
  SI44_RIT_CALL_TAC "H_NTT" [`read X0 s`; SI44_RIT_POLY SI44_T0U; `pc:num`;
                              `read SP s`; `read X30 s`] 32 THEN
  MLD_LAZY_REPOLY_TAC (mk_comb(`mld_poly_ntt`,SI44_RIT_POLY SI44_T0U))
    (SI44_RIT_POLY SI44_T0H) [MLD_POLY_OF_POLYVEC_MAP] THEN
  ARM_STEPS_TAC SI44_RIT_EXEC (33--35) THEN
  SI44_RIT_CALL_TAC "H_PWM42" [`word_add fp (word 9056):int64`;
    `word_add fp (word 3168):int64`; SI44_RIT_POLY SI44_T0H; `cphat:num->int32`;
    `pc:num`] 36 THEN
  ARM_STEPS_TAC SI44_RIT_EXEC (37--39) THEN
  SI44_RIT_CALL_TAC "H_INV" [`read X0 s`; SI44_RIT_PW2; `pc:num`; `read SP s`;
                              `read X30 s`] 40 THEN
  ARM_STEPS_TAC SI44_RIT_EXEC (41--43) THEN
  SI44_RIT_CALL_TAC "H_RED43" [`word_add fp (word 9056):int64`;
    mk_comb(`mld_poly_invntt_tomont`,SI44_RIT_PW2); `pc:num`] 44 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_ct0]) THEN
  ARM_STEPS_TAC SI44_RIT_EXEC (45--48) THEN
  SI44_ADRP_STEPS_TAC SI44_RIT_EXEC (49--54) THEN
  SI44_REG_FORM_TAC "X13" 54 `word_zx (word 95232:int32):int64` THEN
  SI44_REG_FORM_TAC "X8" 54 `word_zx (word 0:int32):int64` THEN
  SI44_RIT_CALL_TAC "H_CHK44" [`word_add fp (word 9056):int64`;
    SI44_RIT_CT0; `word 95232:int32`; `word 0:int32`; `pc:num`] 55 THEN
  ARM_STEPS_TAC SI44_RIT_EXEC [56] THEN
  SI44_DECIDE_TAC `ok2:bool` THEN SI44_CASES_TAC `ok2:bool` THENL
   [ALL_TAC; SI44_RIT_FAIL_TAC `ok2:bool`];;

let SI44_RIT_LAST = prove
 (`!j. j < 4 ==> (j + 1 = 4 <=> ~(j + 1 < 4))`, ARITH_TAC);;

(*** The sum of the row and the back edge ***)

let SI44_RIT_PART3_TAC =
  SI44_RIT_CALL_TAC "H_RADD" [`fp:int64`; `word_add fp (word (4192 + 1024 * j)):int64`;
    SI44_RIT_R0; SI44_RIT_CT0; `j:num`; `96 * j`;
    `word_add fp (word (4192 + 1024 * j)):int64`; `word (6 + 416 * j):int64`;
    `word_add fp (word (4208 + 1024 * j)):int64`; `pc:num`] 57 THEN
  ARM_STEPS_TAC SI44_RIT_EXEC [58] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `j:num` SI44_RIT_LAST) (ASSUME `j < 4`)]) THEN
  SI44_CASES_TAC `j + 1 < 4` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES; ADD_ASSOC] THEN
      CONV_TAC WORD_RULE THEN NO_TAC) THEN
  SI44_END_TAC;;

let SI44_RIT = prove
 (SI44_RIT_STMT,
  MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n) (SI44_RIT_CALLEES ()) THEN
  CONCRETIZE_F_EVENTS_TAC SI44_RIT_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `ok1:bool`; `ok2:bool`; `sk:int64`;
                       `skb:num->byte`; `fp:int64`; `j:num`; `w:num->int32`;
                       `cphat:num->int32`; `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; fst SI44_RIT_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN SI44_ORIENT_TAC THEN
  FULL_INIT_TAC THEN
  SI44_RIT_PART1_TAC THEN SI44_RIT_PART2_TAC THEN SI44_RIT_PART3_TAC);;

(* ------------------------------------------------------------------------- *)
(* The loop over the rows of w0, for the first m rows, both of whose checks  *)
(* pass (RPRE), from the exit of the loop over z (loop26_exit1), where the   *)
(* code sets up row 0, as gcc's SIGN44_RPRE: row j of w holds w0_j - c s2_j  *)
(* + c t0_j afterwards (mld_sign_hint_x), the rows after the first m are     *)
(* unchanged.                                                                *)
(* ------------------------------------------------------------------------- *)

(*** ORR of a 32-aligned frame address with a small constant (fp + k is    ***)
(*** 32-aligned for the offsets k of the code)                            ***)

let SI44_ORR_THM k c =
  let tm = parse_term(Printf.sprintf
    "aligned 32 (fp:int64)
     ==> word_or (word_add fp (word %d)) (word %d) = word_add fp (word %d)" k c (k+c)) in
  prove(tm, REWRITE_TAC[MLD_WRAP_ALIGNED_16_32] THEN
            W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let SI44_ALIGNED16_32 = prove
 (`!x:int64. aligned 32 x ==> aligned 16 x`,
  REWRITE_TAC[MLD_WRAP_ALIGNED_16_32] THEN
  GEN_TAC THEN W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let SI44_RPRE_HX = list_mk_comb(`mld_sign_hint_x 4 mld_poly_decompose_lo_88`,
  [`w:num->int32`; SI44_S2H; SI44_T0H; `cphat:num->int32`]);;

let SI44_RPRE_STMT = parse_term(
 "exists f_events.
    forall e m sk skb fp w cphat pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 32 fp /\\ m <= 4 /\\
      (!j. j < m ==> mld_poly_chknorm (" ^ string_of_term SI44_RIT_R0 ^ ") (word 95154) =
                     word 0 /\\
                     mld_poly_chknorm (" ^ string_of_term SI44_RIT_CT0 ^ ") (word 95232) =
                     word 0) /\\
      ALL (nonoverlapping (word_sub fp (word 1472),12672))
          [(sk,2560); (word pc,libmldsa_size)]
      ==> ensures arm
           (\\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read PC s = word (pc + mldsa44_signature_internal_loop26_exit1) /\\\n" ^
  SI44_RIT_PRE ^ " /\\
                (!i. i < 1024 ==> read (memory :> bytes32 (word_add fp (word (4192 + 4 * i)))) s =
                                  mld_polyvec_map mld_poly_decompose_lo_88 w i) /\\
                read events s = e)
           (\\s. read PC s =
                (if m < 4 then word (pc + mldsa44_signature_internal_loop35)
                 else word (pc + mldsa44_signature_internal_loop35_exit1)) /\\
                read SP s = fp /\\
                read X21 s = word m /\\ read X20 s = word (96 * m) /\\
                read X27 s = word_add fp (word (4192 + 1024 * m)) /\\\n" ^ SI44_PC245760 ^
 "              read (memory :> bytes64 (word_add fp (word 216))) s = word (6 + 416 * m) /\\
                read (memory :> bytes64 (word_add fp (word 224))) s =
                word_add fp (word (4208 + 1024 * m)) /\\
                (!i. i < 256 * m ==> read (memory :> bytes32 (word_add fp (word (4192 + 4 * i)))) s =
                                     " ^ string_of_term SI44_RPRE_HX ^ " i) /\\
                (!i. 256 * m <= i /\\ i < 1024
                     ==> read (memory :> bytes32 (word_add fp (word (4192 + 4 * i)))) s =
                         mld_polyvec_map mld_poly_decompose_lo_88 w i) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events m sk fp pc /\\
                   memaccess_inbounds e2
                    [sk,2560; word_sub fp (word 1472),12672;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa44_signature_internal_consts),128]
                    [word_sub fp (word 1472),12672]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [X18; X19; X20; X21; X27; X30] ,,
            MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
            MAYCHANGE [memory :> bytes(word_sub fp (word 208),208);
                       memory :> bytes(word_add fp (word 216),16);
                       memory :> bytes(word_add fp (word 272),16);
                       memory :> bytes(word_add fp (word 320),416);
                       memory :> bytes(word_add fp (word 4192),4096);
                       memory :> bytes(word_add fp (word 9056),1024)])");;

let SI44_RPRE_EXEC = SI44_EXEC_RANGE "loop26_exit1" "loop35_exit1";;

let SI44_RPRE_INV = parse_term(
 "\\i s. read X21 s = word i /\\ read X20 s = word (96 * i) /\\
        read X27 s = word_add fp (word (4192 + 1024 * i)) /\\\n" ^ SI44_PC245760 ^
 "      read (memory :> bytes64 (word_add fp (word 216))) s = word (6 + 416 * i) /\\
        read (memory :> bytes64 (word_add fp (word 224))) s =
        word_add fp (word (4208 + 1024 * i)) /\\\n" ^ SI44_RIT_PRE ^ " /\\
        (!k. k < 256 * i ==> read (memory :> bytes32 (word_add fp (word (4192 + 4 * k)))) s =
                             " ^ string_of_term SI44_RPRE_HX ^ " k) /\\
        (!k. 256 * i <= k /\\ k < 1024
             ==> read (memory :> bytes32 (word_add fp (word (4192 + 4 * k)))) s =
                 mld_polyvec_map mld_poly_decompose_lo_88 w k)");;

(*** The PC after row i of the first m <= 4 rows, from that of RIT ***)

let SI44_RPRE_PC = prove
 (`!i m a b. i < m /\ m <= 4
             ==> (if i + 1 < 4 then word a else word b):int64 =
                 word (if i + 1 < m then a else if m < 4 then a else b)`,
  REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMPLE_ARITH_TAC);;

(*** The setup of row 0 (15 instructions, the ADRPs at steps 9 to 14) ***)

let SI44_RPRE_SETUP_TAC =
  ARM_STEPS_TAC SI44_RPRE_EXEC (1--8) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SI44_ORR_THM 4192 16) (ASSUME `aligned 32 (fp:int64)`)]) THEN
  SI44_ADRP_STEPS_TAC SI44_RPRE_EXEC (9--14) THEN
  ARM_STEPS_TAC SI44_RPRE_EXEC [15];;

let SI44_RPRE_ALLOWED = [`sk:int64`; `fp:int64`; `pc:num`; `i:num`];;

(*** The events at the end of a loop iteration (SIGN_LOOP_DISCHARGE_TAC with ***)
(*** fp normalized for the safety check)                                   ***)

let SI44_LOOP_MEMACCESS_TAC =
  SIGN_BETA_ALL_TAC THEN SIGN_SPLIT_MEMACCESS_ASM_TAC THEN SI_FB_NORM_TAC 1472 THEN
  REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

let SI44_LOOP_END_TAC =
  SIGN_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [SIGN_LOOP_UNIFY_TAC; SI44_LOOP_MEMACCESS_TAC];;

let SI44_RPRE_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `i < 4` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    can (term_match [] `!j. j < m ==> P j /\ Q j`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FULL_INIT_TAC THEN
  MP_TAC(SPECL [`fp:int64`; `4192`; `1024`; `mld_poly_decompose_lo_88`;
                `w:num->int32`; `i:num`; `s0:armstate`] SIGN_ROW_SLICE) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [`i:num`; `s0:armstate`]
             `!k. 256 * i <= k /\ k < 1024
                  ==> read (memory :> bytes32 (word_add fp (word (4192 + 4 * k)))) s0 = Q k`)
           (concl th)
    then REWRITE_TAC[th] else NO_TAC) THEN
  ANTS_TAC THENL [UNDISCH_TAC `i < 4` THEN ARITH_TAC; STRIP_TAC] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc SI44_RPRE_EXEC "H_RIT"
   [`T`; `T`; `sk:int64`; `skb:num->byte`; `fp:int64`; `i:num`; `w:num->int32`;
    `cphat:num->int32`; `pc:num`] SI44_RPRE_ALLOWED 1 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SI44_RPRE_PC
                               (CONJ (ASSUME `i < m`) (ASSUME `m <= 4`))]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SIGN_ROW_JOIN THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
  (SI44_MAYCHANGE_TAC ORELSE SI44_LOOP_END_TAC);;

(*** The events of a path whose template is already instantiated (e.g. the ***)
(*** case m = 0 after the loop case): e2 is the term itself               ***)

let SI44_CLOSED_END_TAC =
  W(fun (asl,w) ->
    let _,bod = dest_exists w in
    match conjuncts bod with
      [_; eq; _] -> EXISTS_TAC (rhs eq)
    | _ -> failwith "SI44_CLOSED_END_TAC") THEN
  SIGN_BETA_ALL_TAC THEN REWRITE_TAC[ENUMERATEL; APPEND; APPEND_NIL] THEN
  REPEAT CONJ_TAC THEN
  TRY(ASM_REWRITE_TAC[APPEND; APPEND_NIL; GSYM APPEND_ASSOC] THEN NO_TAC) THEN
  SI_FB_NORM_TAC 1472 THEN REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

let SI44_RPRE = prove
 (SI44_RPRE_STMT,
  SI_ASSUME_CALLEE_TAILED_TAC SI44_RIT "H_RIT" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(m:num) (sk:int64) (fp:int64) (pc:num).
     APPEND (f_ev_back m sk fp pc)
      (APPEND (ENUMERATEL m (\i. f_ev_rit sk fp pc i)) (f_ev_front sk fp pc))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `m:num`; `sk:int64`; `skb:num->byte`;
    `fp:int64`; `w:num->int32`; `cphat:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst SI44_RPRE_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SI44_ALIGNED16_32) THEN
  ASM_CASES_TAC `0 < m` THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `m:num`
     `pc + mldsa44_signature_internal_loop35`
     `if m < 4 then pc + mldsa44_signature_internal_loop35
      else pc + mldsa44_signature_internal_loop35_exit1`
     SI44_RPRE_INV THEN
    REPEAT CONJ_TAC THENL
     [SIMPLE_ARITH_TAC;
      REWRITE_TAC[CONJUNCT1 LT; MULT_CLAUSES; ADD_CLAUSES; LE_0] THEN
      FULL_INIT_TAC THEN SI44_RPRE_SETUP_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN SI44_END_TAC;
      SI44_RPRE_BODY_TAC;
      REWRITE_TAC[] THEN FULL_INIT_TAC THEN SIGN_PC_COND_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      SIGN_BETA_ALL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC];
    SUBGOAL_THEN `m = 0` SUBST_ALL_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN SI44_RPRE_SETUP_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ARITH; MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    REWRITE_TAC[ENUMERATEL; APPEND; APPEND_NIL] THEN SI44_CLOSED_END_TAC]);;

(* ------------------------------------------------------------------------- *)
(* s1 in the NTT domain and y, as in the gcc proof (SIGN44_S1H, SIGN44_YY), *)
(* with y sampled from rho'' (RHO, at fp + 2080) with the nonce 4 att + i.   *)
(* ------------------------------------------------------------------------- *)

let SI44_S1U =
 `mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte)(128 + j))`;;
let SI44_S1H = mk_comb(`mld_polyvec_map mld_poly_ntt`,SI44_S1U);;
let SI44_YK = `mld_sign_y mld_poly_uniform_gamma1_17 RHO (4 * att)`;;
let SI44_ZI = list_mk_comb(`mld_sign_z`, [SI44_S1H; `cphat:num->int32`; SI44_YK; `i:num`]);;

(* ------------------------------------------------------------------------- *)
(* One iteration of the loop over z (ZIT), from loop26 with i in x21: s1_i  *)
(* unpacked into fp + 2144 and transformed, its product with the challenge   *)
(* and the inverse NTT, y_i sampled again (the inlined poly_uniform_gamma1   *)
(* with the nonce 4 att + i), the sum, the reduction and the norm check of   *)
(* z_i; if it passes (ok), z_i packed into the signature at sig + 32 + 576 i *)
(* and back to loop26 or, after the last, to loop26_exit1; else to join10.   *)
(* ------------------------------------------------------------------------- *)

let SI44_ZIT_PRE =
 "read SP s = fp /\\
  read X22 s = word_add fp (word 10192) /\\ read X23 s = word_add fp (word 9056) /\\
  read X24 s = word 2 /\\
  read X25 s = word 18446744073701171199 /\\ read X26 s = word_add fp (word 10080) /\\
  read X28 s = word 252236767799803904 /\\
  read (memory :> bytes64 (word_add fp (word 232))) s = word_add fp (word 3168) /\\
  read (memory :> bytes64 (word_add fp (word 800))) s = word_add sk (word 128) /\\
  read (memory :> bytes64 (word_add fp (word 264))) s = word_add fp (word 10513) /\\
  read (memory :> bytes64 (word_add fp (word 10080))) s = word_add fp (word 2080) /\\
  read (memory :> bytes16 (word_add fp (word 10088))) s = word (4 * att) /\\
  read (memory :> bytes128 (word_add fp (word 240))) s =
  word 339618401959998730991157055895298383871 /\\
  read (memory :> bytes128 (word_add fp (word 288))) s =
  word 0xffffff07ffffff06ffffff05ffffff04 /\\
  read (memory :> bytes128 (word_add fp (word 304))) s =
  word 0xffffff03ffffff02ffffff01ffffff00 /\\
  read (memory :> bytes (word_add fp (word 2080),64)) s = RHO /\\
  (!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (3168 + 4 * i)))) s =
                   cphat i) /\\
  (!i. i < 2560 ==> read (memory :> bytes8 (word_add sk (word i))) s = skb i) /\\
  read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
  read (memory :> bytes(ea,el)) s = ev";;

let SI44_ZIT_STMT = parse_term(
 "!mf mc ea el ev.
   memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
   ==> exists f_events.
        forall e ok sig sk skb fp i cphat RHO att pc.
         aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
         aligned 32 fp /\\ i < 4 /\\ att < 16382 /\\
         (ok <=> mld_poly_chknorm (" ^ string_of_term SI44_ZI ^ ") (word 130994) = word 0) /\\
         nonoverlapping (sig,2420) (word_sub fp (word 1472),12672) /\\
         ALL (nonoverlapping (word_sub fp (word 1472),12672))
             [(sk,2560); (word pc,libmldsa_size); (word(pc + got_memset),8);
              (word(pc + got_memcpy),8); (ea,el)] /\\
         ALL (nonoverlapping (sig,2420))
             [(sk,2560); (word pc,libmldsa_size); (word(pc + got_memset),8);
              (word(pc + got_memcpy),8); (ea,el)]
         ==> ensures arm
              (\\s. aligned_bytes_loaded s (word pc)
                     mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                   read PC s = word (pc + mldsa44_signature_internal_loop26) /\\
                   read X21 s = word i /\\ read X27 s = word (96 * i) /\\
                   read X20 s = word_add fp (word 2144) /\\
                   read X1 s = word_add sig (word (40 + 576 * i)) /\\\n" ^ SI44_ZIT_PRE ^ " /\\
                   read events s = e)
              (\\s. read PC s =
                   (if ok then (if i + 1 < 4 then word (pc + mldsa44_signature_internal_loop26)
                                else word (pc + mldsa44_signature_internal_loop26_exit1))
                    else word (pc + mldsa44_signature_internal_join10)) /\\
                   read SP s = fp /\\
                   read X22 s = word_add fp (word 10192) /\\
                   read X26 s = word_add fp (word 10080) /\\
                   (ok ==> read X21 s = word (i + 1) /\\ read X27 s = word (96 * (i + 1)) /\\
                           read X20 s = word_add fp (word 2144) /\\
                           read X1 s = word_add sig (word (40 + 576 * (i + 1))) /\\
                           (!t. t < 576
                                ==> read (memory :> bytes8 (word_add sig (word ((32 + 576 * i) + t)))) s =
                                    mld_polyz_pack_17 (" ^ string_of_term SI44_ZI ^ ") t)) /\\
                   (exists e2.
                      read events s = APPEND e2 e /\\
                      e2 = f_events ok sig sk fp i mf mc pc /\\
                      memaccess_inbounds e2
                       [sig,2420; sk,2560; word_sub fp (word 1472),12672;
                        word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                        word(pc + rodata_mld_KeccakF_RoundConstants),192;
                        word(pc + rodata_mld_zetas),1024;
                        word(pc + mldsa44_signature_internal_consts),128]
                       [sig,2420; word_sub fp (word 1472),12672]))
              (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [X18; X19; X20; X21; X22; X26; X27; X30] ,,
               MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
               MAYCHANGE [memory :> bytes(word_sub fp (word 240),240);
                          memory :> bytes(word_add fp (word 320),416);
                          memory :> bytes(word_add fp (word 2144),1024);
                          memory :> bytes(word_add fp (word 9056),1024);
                          memory :> bytes(word_add fp (word 10192),984);
                          memory :> bytes(word_add sig (word (32 + 576 * i)),576)])");;

let SI44_ZIT_EXEC = SI44_EXEC_RANGE "loop26" "loop26_exit1";;

let SI44_ZIT_TEMPLATE =
 `\(ok:bool) (sig:int64) (sk:int64) (fp:int64) (i:num) (mf:int64) (mc:int64) (pc:num).
   if ok then (if i + 1 < 4 then f_ev_mid sig sk fp i mf mc pc
               else f_ev_last sig sk fp i mf mc pc)
   else f_ev_f sig sk fp i mf mc pc :(uarch_event)list`;;

let SI44_ZIT_ALLOWED = [`ok:bool`; `sig:int64`; `sk:int64`; `fp:int64`; `i:num`;
                        `mf:int64`; `mc:int64`; `pc:num`];;

let SI44_ZIT_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc SI44_ZIT_EXEC
    name ilist SI44_ZIT_ALLOWED n;;

(*** Bytes of the key at base + (aoff + k), the value skb (voff + k), with ***)
(*** the index variable idx < 4                                           ***)

let SI44_SLICE_GEN_TAC base idx aoff voff n st =
  let t = vsubst [st,`s:armstate`] (parse_term(Printf.sprintf
   "!k. k < %d ==> read (memory :> bytes8 (word_add %s (word (%s + k)))) s =
                   (skb:num->byte) (%s + k)" n base aoff voff)) in
  let ilt = parse_term(Printf.sprintf "%s < 4" idx) in
  SUBGOAL_THEN t ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[GSYM ADD_ASSOC] THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (term_match []
       `!i. i < 2560 ==> read (memory :> bytes8 (word_add sk (word i))) s = skb i`)
       (concl th))) THEN
    MAP_EVERY UNDISCH_TAC [ilt; mk_binop `(<):num->num->bool` `k:num` (mk_small_numeral n)] THEN
    ARITH_TAC;
    ALL_TAC];;

(*** The 16-bit nonce as ldrh loads it ***)

let SI44_ZX16 = prove
 (`!n. n < 65536 ==> word_zx (word_zx (word n:int16):int32):int64 = word n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_16; DIMINDEX_32;
              DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `n MOD 65536 = n /\ n MOD 4294967296 = n /\
                n MOD 18446744073709551616 = n` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_REWRITE_TAC[]]);;

(*** The frame of the inlined poly_uniform_gamma1 (fr = fp - 240) in the    ***)
(*** forms of fp                                                            ***)

let SI44_FR_EQS =
  map (fun k ->
    let tm = if k = 240 then `word_add (word_sub fp (word 240)) (word 240):int64 = fp`
      else parse_term(Printf.sprintf
        "word_add (word_sub fp (word 240)) (word %d):int64 = word_add fp (word %d)"
        k (k - 240)) in
    WORD_RULE tm) [240; 10432; 9296; 504; 10753; 528; 544] @
  map (fun k ->
    prove(parse_term(Printf.sprintf
      "!t. word_add (word_sub fp (word 240)) (word (%d + t)):int64 =
           word_add fp (word (%d + t))" k (k - 240)),
     GEN_TAC THEN REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE)) [9296; 10432];;

let SI44_ZTEST4 = prove
 (`!i. i < 4
       ==> (val (word_add (word i) (word 18446744073709551613):int64) = 0 <=>
            ~(i + 1 < 4))`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let SI44_ZIT_POLY v = mk_comb(mk_comb(`mld_poly_of`,v),`i:num`);;
let SI44_ZIT_PW = list_mk_comb(`mld_poly_pointwise_montgomery`,
  [SI44_ZIT_POLY SI44_S1H; `cphat:num->int32`]);;
let SI44_ZIT_CS1 = mk_comb(`mld_poly_invntt_tomont`,SI44_ZIT_PW);;
let SI44_ZIT_Y = SI44_ZIT_POLY SI44_YK;;

let SI44_ZIT = prove
 (SI44_ZIT_STMT,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP SI44_G1_Z th) "H_G1" THEN
    MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
     [SI44_ETA_ZTH,"H_ETA";
      MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_NTT";
      MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_INV";
      SI44_RIT_LK SI44_PWM "loop29","H_PWM29"; SI44_ZADD,"H_ZADD";
      SI44_RIT_LK SI44_RED "loop32","H_RED32"; SI44_RIT_LK SI44_CHK "loop33","H_CHK33";
      SI44_ZPACK,"H_ZPACK"]) THEN
  CONCRETIZE_F_EVENTS_TAC SI44_ZIT_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `ok:bool`; `sig:int64`; `sk:int64`;
    `skb:num->byte`; `fp:int64`; `i:num`; `cphat:num->int32`; `RHO:num`; `att:num`;
    `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; fst SI44_ZIT_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SI44_ALIGNED16_32) THEN
  FIRST_X_ASSUM(fun th -> if is_iff(concl th) && lhs(concl th) = `ok:bool`
                          then ASSUME_TAC(GSYM th) else NO_TAC) THEN
  FULL_INIT_TAC THEN
  (*** s1_i, its NTT, the product and the inverse NTT ***)
  SI44_SLICE_GEN_TAC "sk" "i" "128 + 96 * i" "128 + 96 * i" 96 `s0:armstate` THEN
  SI44_ZIT_CALL_TAC "H_ETA" [`fp:int64`; `word_add sk (word 128):int64`; `i:num`;
    `\k. (skb:num->byte) (128 + 96 * i + k)`; `word_add sig (word (40 + 576 * i)):int64`;
    `pc:num`] 1 THEN
  MLD_LAZY_REPOLY_TAC `mld_polyeta_unpack_2 (\k. (skb:num->byte) (128 + 96 * i + k))`
    (SI44_ZIT_POLY SI44_S1U) [mld_polyvec_unpack; MLD_POLY_OF_POLYVEC] THEN
  ARM_STEPS_TAC SI44_ZIT_EXEC (2--3) THEN
  SI44_ZIT_CALL_TAC "H_NTT" [`read X0 s`; SI44_ZIT_POLY SI44_S1U; `pc:num`;
                              `read SP s`; `read X30 s`] 4 THEN
  MLD_LAZY_REPOLY_TAC (mk_comb(`mld_poly_ntt`,SI44_ZIT_POLY SI44_S1U))
    (SI44_ZIT_POLY SI44_S1H) [MLD_POLY_OF_POLYVEC_MAP] THEN
  ARM_STEPS_TAC SI44_ZIT_EXEC (5--6) THEN
  SI44_ZIT_CALL_TAC "H_PWM29" [`word_add fp (word 2144):int64`;
    `word_add fp (word 3168):int64`; SI44_ZIT_POLY SI44_S1H; `cphat:num->int32`;
    `pc:num`] 7 THEN
  ARM_STEPS_TAC SI44_ZIT_EXEC (8--9) THEN
  SI44_ZIT_CALL_TAC "H_INV" [`read X0 s`; SI44_ZIT_PW; `pc:num`; `read SP s`;
                              `read X30 s`] 10 THEN
  (*** y_i ***)
  ARM_STEPS_TAC SI44_ZIT_EXEC (11--16) THEN
  SUBGOAL_THEN `4 * att < 65536` ASSUME_TAC THENL
   [UNDISCH_TAC `att < 16382` THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `4 * att` SI44_ZX16)
                                 (ASSUME `4 * att < 65536`)]) THEN
  MAP_EVERY ASSUME_TAC SI44_FR_EQS THEN
  SI44_ZIT_CALL_TAC "H_G1" [`word_add fp (word 2080):int64`; `RHO:num`; `4 * att`;
    `i:num`; `word_sub fp (word 240):int64`; `pc:num`] 17 THEN
  RULE_ASSUM_TAC(REWRITE_RULE SI44_FR_EQS) THEN
  MLD_LAZY_REPOLY_TAC `mld_poly_uniform_gamma1_17 RHO (word (4 * att + i))` SI44_ZIT_Y
    [mld_sign_y; MLD_POLY_OF_POLYVEC] THEN
  (*** z_i = c s1_i + y_i, reduced, and its check ***)
  ARM_STEPS_TAC SI44_ZIT_EXEC (18--33) THEN
  SI44_ZIT_CALL_TAC "H_ZADD" [`fp:int64`; SI44_ZIT_CS1; SI44_ZIT_Y; `i:num`; `pc:num`] 34 THEN
  SI44_ZIT_CALL_TAC "H_RED32" [`word_add fp (word 2144):int64`;
    list_mk_comb(`mld_poly_add`,[SI44_ZIT_CS1; SI44_ZIT_Y]); `pc:num`] 35 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_z]) THEN
  ARM_STEPS_TAC SI44_ZIT_EXEC (36--41) THEN
  SI44_REG_FORM_TAC "X13" 41 `word_zx (word_sub (word 130994:int32) (word 1)):int64` THEN
  SI44_REG_FORM_TAC "X8" 41 `word_zx (word 0:int32):int64` THEN
  SI44_ZIT_CALL_TAC "H_CHK33" [`word_add fp (word 2144):int64`; SI44_ZI;
    `word 130994:int32`; `word 0:int32`; `pc:num`] 42 THEN
  ARM_STEPS_TAC SI44_ZIT_EXEC [43] THEN
  SI44_DECIDE_TAC `ok:bool` THEN SI44_CASES_TAC `ok:bool` THENL
   [ALL_TAC; SI44_RIT_FAIL_TAC `ok:bool`] THEN
  (*** the packing of z_i and the back edge ***)
  ARM_STEPS_TAC SI44_ZIT_EXEC (44--46) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SI44_ORR_THM 2144 8) (ASSUME `aligned 32 (fp:int64)`)]) THEN
  SI44_REG_FORM_TAC "X8" 46 `word_add sig (word ((32 + 576 * i) + 8)):int64` THEN
  SI44_ZIT_CALL_TAC "H_ZPACK" [`word_add sig (word (32 + 576 * i)):int64`;
    `word_add fp (word 2144):int64`; SI44_ZI; `pc:num`] 47 THEN
  ARM_STEPS_TAC SI44_ZIT_EXEC (48--56) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `i:num` SI44_ZTEST4) (ASSUME `i < 4`)]) THEN
  SI44_CASES_TAC `i + 1 < 4` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES; ADD_ASSOC] THEN
      CONV_TAC WORD_RULE THEN NO_TAC) THEN
  SI44_END_TAC);;

(* ------------------------------------------------------------------------- *)
(* The loop over z, for the first m polynomials, each of which passes the    *)
(* norm check (ZPRE), from after the NTT of the challenge, where the code    *)
(* sets up i = 0, as gcc's SIGN44_ZPRE: the first 576 m bytes of z packed    *)
(* are in the signature at sig + 32.                                         *)
(* ------------------------------------------------------------------------- *)

let SI44_ZPRE_Z = list_mk_comb(`mld_sign_z`, [SI44_S1H; `cphat:num->int32`; SI44_YK]);;
let SI44_ZPRE_ZI = mk_comb(SI44_ZPRE_Z,`i:num`);;

let SI44_ZPRE_STMT = parse_term(
 "!mf mc ea el ev.
   memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
   ==> exists f_events.
        forall e m sig sk skb fp cphat RHO att pc.
         aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
         aligned 32 fp /\\ m <= 4 /\\ att < 16382 /\\
         (!i. i < m ==> mld_poly_chknorm (" ^ string_of_term SI44_ZPRE_ZI ^ ") (word 130994) =
                        word 0) /\\
         nonoverlapping (sig,2420) (word_sub fp (word 1472),12672) /\\
         ALL (nonoverlapping (word_sub fp (word 1472),12672))
             [(sk,2560); (word pc,libmldsa_size); (word(pc + got_memset),8);
              (word(pc + got_memcpy),8); (ea,el)] /\\
         ALL (nonoverlapping (sig,2420))
             [(sk,2560); (word pc,libmldsa_size); (word(pc + got_memset),8);
              (word(pc + got_memcpy),8); (ea,el)]
         ==> ensures arm
              (\\s. aligned_bytes_loaded s (word pc)
                     mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                   read PC s = word (pc + mldsa44_signature_internal_after_mldsa_poly_ntt_2) /\\
                   read X20 s = word_add fp (word 2144) /\\
                   read (memory :> bytes64 (word_add fp (word 192))) s = sig /\\\n" ^
  SI44_ZIT_PRE ^ " /\\
                   read events s = e)
              (\\s. read PC s =
                   (if m < 4 then word (pc + mldsa44_signature_internal_loop26)
                    else word (pc + mldsa44_signature_internal_loop26_exit1)) /\\
                   read SP s = fp /\\
                   read X21 s = word m /\\ read X27 s = word (96 * m) /\\
                   read X20 s = word_add fp (word 2144) /\\
                   read X1 s = word_add sig (word (40 + 576 * m)) /\\
                   read X22 s = word_add fp (word 10192) /\\
                   read X26 s = word_add fp (word 10080) /\\
                   (!t. t < 576 * m
                        ==> read (memory :> bytes8 (word_add sig (word (32 + t)))) s =
                            mld_polyvec_pack 576 mld_polyz_pack_17
                             (mld_polyvec (" ^ string_of_term SI44_ZPRE_Z ^ ")) t) /\\
                   (exists e2.
                      read events s = APPEND e2 e /\\
                      e2 = f_events m sig sk fp mf mc pc /\\
                      memaccess_inbounds e2
                       [sig,2420; sk,2560; word_sub fp (word 1472),12672;
                        word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                        word(pc + rodata_mld_KeccakF_RoundConstants),192;
                        word(pc + rodata_mld_zetas),1024;
                        word(pc + mldsa44_signature_internal_consts),128]
                       [sig,2420; word_sub fp (word 1472),12672]))
              (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [X18; X19; X20; X21; X22; X26; X27; X30] ,,
               MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
               MAYCHANGE [memory :> bytes(word_sub fp (word 240),240);
                          memory :> bytes(word_add fp (word 320),416);
                          memory :> bytes(word_add fp (word 2144),1024);
                          memory :> bytes(word_add fp (word 9056),1024);
                          memory :> bytes(word_add fp (word 10192),984);
                          memory :> bytes(word_add sig (word 32),2304)])");;

let SI44_ZPRE_EXEC = SI44_EXEC_RANGE "after_mldsa_poly_ntt_2" "loop26_exit1";;

let SI44_ZPRE_INV = parse_term(
 "\\i s. read X21 s = word i /\\ read X27 s = word (96 * i) /\\
        read X20 s = word_add fp (word 2144) /\\
        read X1 s = word_add sig (word (40 + 576 * i)) /\\
        read (memory :> bytes64 (word_add fp (word 192))) s = sig /\\\n" ^ SI44_ZIT_PRE ^ " /\\
        (!t. t < 576 * i
             ==> read (memory :> bytes8 (word_add sig (word (32 + t)))) s =
                 mld_polyvec_pack 576 mld_polyz_pack_17
                  (mld_polyvec (" ^ string_of_term SI44_ZPRE_Z ^ ")) t)");;

let SI44_ZPRE_ALLOWED = [`sig:int64`; `sk:int64`; `fp:int64`; `mf:int64`; `mc:int64`;
                         `pc:num`; `i:num`];;

let SI44_ZPRE_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `i < 4` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o C MP (ASSUME `i < m`) o SPEC `i:num` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `mld_poly_chknorm`)) (concl th))) THEN
  FULL_INIT_TAC THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc SI44_ZPRE_EXEC "H_ZIT"
   [`T`; `sig:int64`; `sk:int64`; `skb:num->byte`; `fp:int64`; `i:num`;
    `cphat:num->int32`; `RHO:num`; `att:num`; `pc:num`] SI44_ZPRE_ALLOWED 1 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SI44_RPRE_PC
                               (CONJ (ASSUME `i < m`) (ASSUME `m <= 4`))]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC(ISPECL [`mld_polyz_pack_17`; `576`] SIGN_PACK_JOIN) THEN
      ASM_REWRITE_TAC[SIGN_POLYZ_PACK_17_LOCAL] THEN
      REWRITE_TAC[ADD_ASSOC] THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
  (SI44_MAYCHANGE_TAC ORELSE SI44_LOOP_END_TAC);;

let SI44_ZPRE_SETUP_TAC = ARM_STEPS_TAC SI44_ZPRE_EXEC (1--4);;

let SI44_ZPRE = prove
 (SI44_ZPRE_STMT,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    SI_ASSUME_CALLEE_TAILED_TAC (MATCH_MP SI44_ZIT th) "H_ZIT") THEN
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
              fst SI44_ZPRE_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SI44_ALIGNED16_32) THEN
  ASM_CASES_TAC `0 < m` THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `m:num`
     `pc + mldsa44_signature_internal_loop26`
     `if m < 4 then pc + mldsa44_signature_internal_loop26
      else pc + mldsa44_signature_internal_loop26_exit1`
     SI44_ZPRE_INV THEN
    REPEAT CONJ_TAC THENL
     [SIMPLE_ARITH_TAC;
      REWRITE_TAC[CONJUNCT1 LT; MULT_CLAUSES; ADD_CLAUSES; LE_0] THEN
      FULL_INIT_TAC THEN SI44_ZPRE_SETUP_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN SI44_END_TAC;
      SI44_ZPRE_BODY_TAC;
      REWRITE_TAC[] THEN FULL_INIT_TAC THEN SIGN_PC_COND_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      SIGN_BETA_ALL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC];
    SUBGOAL_THEN `m = 0` SUBST_ALL_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN SI44_ZPRE_SETUP_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ARITH; MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    REWRITE_TAC[ENUMERATEL; APPEND; APPEND_NIL] THEN SI44_CLOSED_END_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The end of the start of an attempt (HPOST), from the exit of the loop     *)
(* over the columns of y (loop3_exit), where row k of w holds the sums       *)
(* mld_lazy_acc rho k y^ 3: the zeroing of the seed of the matrix, the       *)
(* reduction, the inverse NTT and caddq of each row (mld_sign_w, by          *)
(* MLD_LAZY_SIGN_W), the decomposition of each row with w0 in place and w1   *)
(* packed at fp + 8288 + 192 k, c~ = SHAKE256(mu || w1) at fp + 10112 by     *)
(* mld_H44, the challenge at fp + 3168 and its NTT.                          *)
(* ------------------------------------------------------------------------- *)

(*** Row k of the vector of the sums, and the vectors that the reduction, ***)
(*** the inverse NTT and caddq give from it                                ***)

let SI44_YH = `mld_polyvec_map mld_poly_ntt (mld_sign_y mld_poly_uniform_gamma1_17 RHO (4 * att))`;;
let SI44_W = `mld_sign_w 4 (mld_polyvec_matrix_expand 4 rho)
               (mld_sign_y mld_poly_uniform_gamma1_17 RHO (4 * att))`;;
let SI44_W1 = mk_comb(`mld_sign_w1 (mld_polyw1_pack_88 o mld_poly_decompose_hi_88) 192`,SI44_W);;
let SI44_CT = mk_comb(`mld_sign_ctilde 4 192 MU`,SI44_W1);;
let SI44_CTN = mk_comb(`num_of_bytelist`,list_mk_comb(`list_of_seq:(num->byte)->num->byte list`,
                                                     [SI44_CT; `32`]));;

let SI44_ACC_ROWS = String.concat "" (map (fun k -> Printf.sprintf
  "(!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (%d + 4 * i)))) s =
                   mld_lazy_acc rho %d (%s) 3 i) /\\\n" (4192 + 1024 * k) k
  (string_of_term SI44_YH)) (0--3));;

let SI44_HPOST_STMT = parse_term(
 "!mf mc ea el ev.
   memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
   ==> exists f_events.
        forall e fp rho RHO MU att C guard pc.
         aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
         aligned 32 fp /\\ att < 16382 /\\ mld_matrix_terminates 4 4 rho /\\
         " ^ string_of_term SI44_CTN ^ " = C /\\
         mld_poly_challenge_terminates 39 32 C /\\
         ALL (nonoverlapping (word_sub fp (word 1472),12672))
             [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8); (guard,8);
              (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
         ==> ensures arm
              (\\s. aligned_bytes_loaded s (word pc)
                     mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                   read PC s = word (pc + mldsa44_signature_internal_loop3_exit) /\\
                   read SP s = fp /\\
                   read X19 s = word_add fp (word 4192) /\\ read X23 s = word_add fp (word 9056) /\\
                   read (memory :> bytes128 (word_add fp (word 240))) s =
                   word 339618401959998730991157055895298383871 /\\\n" ^
  SI44_SLOT_FACTS [56,9008; 64,8960; 72,8912; 80,8816; 88,8768; 96,8720; 104,8624;
                   112,8576; 120,8528; 128,8432; 136,8384; 144,8336;
                   168,8864; 176,8672; 184,8480] ^
  SI44_ACC_ROWS ^
 "                 read (memory :> bytes (word_add fp (word 2016),64)) s = MU /\\
                   read (memory :> bytes64(word(pc + got_stack_chk_guard))) s = guard /\\
                   read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                   read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                   read (memory :> bytes(ea,el)) s = ev /\\
                   read events s = e)
              (\\s. read PC s = word (pc + mldsa44_signature_internal_after_mldsa_poly_ntt_2) /\\
                   read SP s = fp /\\
                   read X20 s = word_add fp (word 2144) /\\
                   (!i. i < 1024 ==> read (memory :> bytes32 (word_add fp (word (4192 + 4 * i)))) s =
                                     mld_polyvec_map mld_poly_decompose_lo_88 (" ^
                                       string_of_term SI44_W ^ ") i) /\\
                   (!j. j < 768 ==> read (memory :> bytes8 (word_add fp (word (8288 + j)))) s =
                                    " ^ string_of_term SI44_W1 ^ " j) /\\
                   read (memory :> bytes (word_add fp (word 10112),32)) s = C /\\
                   (!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (3168 + 4 * i)))) s =
                                    mld_sign_cphat 39 32 (" ^ string_of_term SI44_CT ^ ") i) /\\
                   (exists e2.
                      read events s = APPEND e2 e /\\
                      e2 = f_events fp guard mf mc pc C /\\
                      memaccess_inbounds e2
                       [word_sub fp (word 1472),12672;
                        word(pc + got_stack_chk_guard),8; guard,8;
                        word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                        word(pc + rodata_mld_KeccakF_RoundConstants),192;
                        word(pc + rodata_mld_zetas),1024;
                        word(pc + mldsa44_signature_internal_consts),128]
                       [word_sub fp (word 1472),12672]))
              (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [X18; X19; X20; X21; X27; X30] ,,
               MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
               MAYCHANGE [memory :> bytes(word_sub fp (word 768),768);
                          memory :> bytes(word_add fp (word 528),208);
                          memory :> bytes(word_add fp (word 3168),1024);
                          memory :> bytes(word_add fp (word 4192),4096);
                          memory :> bytes(word_add fp (word 8288),768);
                          memory :> bytes(word_add fp (word 9056),1024);
                          memory :> bytes(word_add fp (word 10112),64)])");;

let SI44_HPOST_EXEC = SI44_EXEC_RANGE "loop3_exit" "after_mldsa_poly_ntt_2";;

let SI44_HV = mk_comb(`mld_polyvec`,mk_abs(`i:num`,
  list_mk_comb(`mld_lazy_acc`,[`rho:num`; `i:num`; SI44_YH; `3`])));;
let SI44_HV1 = mk_comb(`mld_polyvec_map mld_poly_reduce`,SI44_HV);;
let SI44_HV2 = mk_comb(`mld_polyvec_map mld_poly_invntt_tomont`,SI44_HV1);;
let SI44_YVL = `mld_polyvec_matrix_yvec_lazy 4 rho
                 (mld_sign_y mld_poly_uniform_gamma1_17 RHO (4 * att))`;;
let SI44_HV3 = mk_comb(`mld_polyvec_map mld_poly_caddq`,SI44_YVL);;

let SI44_YVL_EQ = prove
 (mk_eq(SI44_YVL,SI44_HV2),
  REWRITE_TAC[mld_polyvec_matrix_yvec_lazy] THEN CONV_TAC NUM_REDUCE_CONV);;

let SI44_HPOLY v k = mk_comb(mk_comb(`mld_poly_of`,v),mk_small_numeral k);;

(*** caddq of the product is w (MLD_LAZY_SIGN_W), and row k as row k of w ***)

let SI44_WEQ = mk_forall(`j:num`,mk_imp(`j < 1024`,
  mk_eq(mk_comb(SI44_HV3,`j:num`),mk_comb(SI44_W,`j:num`))));;

let SI44_WEQ_TAC =
  SUBGOAL_THEN SI44_WEQ ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`4`; `4`; `rho:num`;
                  `mld_sign_y mld_poly_uniform_gamma1_17 RHO (4 * att)`; `j:num`]
                 MLD_LAZY_SIGN_W) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    ASM_REWRITE_TAC[MLD_LAZY_SIGN_Y_BOUND];
    ALL_TAC];;

let SI44_W_TAC k =
  let old = SI44_HPOLY SI44_HV3 k and nw = SI44_HPOLY SI44_W k in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_forall c && can (find_term ((=) old)) c then
      let iv,_ = dest_forall c in
      SUBGOAL_THEN (subst [nw,old] c) ASSUME_TAC THENL
       [X_GEN_TAC iv THEN DISCH_THEN(fun ith ->
          REWRITE_TAC[MP (SPEC iv th) ith] THEN REWRITE_TAC[mld_poly_of] THEN
          FIRST_ASSUM(fun wth -> if concl wth = SI44_WEQ then MATCH_MP_TAC wth
                                 else NO_TAC) THEN
          MP_TAC ith THEN ARITH_TAC);
        ALL_TAC]
    else NO_TAC);;

(*** Row k at fp + 4192 + 1024 k as the offset loops (base x19 = fp + 4192) ***)
(*** state it, and back                                                      ***)

let SI44_ROW_EQS = map (fun k ->
  prove(parse_term(Printf.sprintf
    "!i. word_add (word_add fp (word 4192)) (word (%d + 4 * i)):int64 =
         word_add fp (word (%d + 4 * i))" (1024 * k) (4192 + 1024 * k)),
   GEN_TAC THEN REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE)) (1--3);;

let SI44_NEST_TAC k v =
  let eqth = el (k - 1) SI44_ROW_EQS in
  let pat = parse_term(Printf.sprintf "word_add fp (word (%d + 4 * i)):int64"
                                      (4192 + 1024 * k)) in
  FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) pat)) (concl th) &&
                           can (find_term ((=) v)) (concl th)
    then ASSUME_TAC(REWRITE_RULE[GSYM eqth] th) else NO_TAC);;

let SI44_CROW_EQS = map (fun k ->
  prove(parse_term(Printf.sprintf
    "!i. word_add fp (word (4192 + %d + 4 * i)):int64 = word_add fp (word (%d + 4 * i))"
    (1024 * k) (4192 + 1024 * k)),
   GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC)) (1--3);;

let SI44_CNEST_TAC k v =
  let eqth = el (k - 1) SI44_CROW_EQS in
  let pat = parse_term(Printf.sprintf "word_add fp (word (%d + 4 * i)):int64"
                                      (4192 + 1024 * k)) in
  FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) pat)) (concl th) &&
                           can (find_term ((=) v)) (concl th)
    then ASSUME_TAC(REWRITE_RULE[GSYM eqth] th) else NO_TAC);;

(*** Rewriting the facts only: rewriting the assumed callee theorems too    ***)
(*** makes a later FULL_CALL_TAC fail with "MATCH_MP_TAC: No match"         ***)

let SI44_ASM_RW_TAC ths =
  RULE_ASSUM_TAC(fun th ->
    if can (find_term (fun t -> is_const t && fst(dest_const t) = "ensures")) (concl th)
    then th else REWRITE_RULE ths th);;

let SI44_FLAT_TAC = SI44_ASM_RW_TAC (SI44_ROW_EQS @ SI44_CROW_EQS);;

let SI44_HCALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc SI44_HPOST_EXEC
    name ilist [`fp:int64`; `guard:int64`; `mf:int64`; `mc:int64`; `pc:num`; `C:num`] n;;

let SI44_FPK k = parse_term(Printf.sprintf "word_add fp (word %d):int64" (4192 + 1024 * k));;

let SI44_REPOLY_MAP_TAC f v1 v2 k =
  MLD_LAZY_REPOLY_TAC (mk_comb(f,SI44_HPOLY v1 k)) (SI44_HPOLY v2 k)
    [MLD_POLY_OF_POLYVEC_MAP];;

let SI44_HPOST_CALLEES ms mcp =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    (MATCH_MP MLDSA_NATIVE_H_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL mcp)
    "H_H44" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    (MATCH_MP MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL ms)
    "H_CHAL" THEN
  MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
   ([MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_NTT";
     MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_INV"] @
    map (fun k -> SI44_RIT_LK SI44_RED ("loop" ^ string_of_int (14 + k)),
                  "H_RED" ^ string_of_int k) (0--3) @
    map (fun k -> SI44_RIT_LK SI44_CADDQ ("loop" ^ string_of_int (18 + k)),
                  "H_CADDQ" ^ string_of_int k) (0--3) @
    map (fun k -> SI44_RIT_LK SI44_DEC ("loop" ^ string_of_int (22 + k)),
                  "H_DEC" ^ string_of_int k) (0--3) @
    map (fun k -> el k SI44_W1PS, "H_W1PS" ^ string_of_int k) (0--3));;

let SI44_HPOST_RED_TAC k n =
  (if k = 0 then ALL_TAC else SI44_NEST_TAC k (SI44_HPOLY SI44_HV k)) THEN
  SI44_HCALL_TAC ("H_RED" ^ string_of_int k)
    [SI44_FPK 0; SI44_HPOLY SI44_HV k; `pc:num`] n THEN SI44_FLAT_TAC THEN
  SI44_REPOLY_MAP_TAC `mld_poly_reduce` SI44_HV SI44_HV1 k;;

let SI44_HPOST_INV_TAC k n =
  SI44_HCALL_TAC "H_INV" [`read X0 s`; SI44_HPOLY SI44_HV1 k; `pc:num`;
                          `read SP s`; `read X30 s`] n THEN
  SI44_REPOLY_MAP_TAC `mld_poly_invntt_tomont` SI44_HV1 SI44_HV2 k;;

let SI44_HPOST_CADDQ_TAC k n =
  (if k = 0 then ALL_TAC else SI44_CNEST_TAC k (SI44_HPOLY SI44_YVL k)) THEN
  SI44_HCALL_TAC ("H_CADDQ" ^ string_of_int k) [SI44_FPK 0; SI44_HPOLY SI44_YVL k; `pc:num`] n THEN
  SI44_FLAT_TAC THEN
  SI44_REPOLY_MAP_TAC `mld_poly_caddq` SI44_YVL SI44_HV3 k THEN SI44_W_TAC k;;

let SI44_HPOST_PART1_TAC =
  MAP_EVERY (fun k -> MLD_LAZY_REPOLY_TAC
     (list_mk_comb(`mld_lazy_acc`,[`rho:num`; mk_small_numeral k; SI44_YH; `3`]))
     (SI44_HPOLY SI44_HV k) [MLD_POLY_OF_POLYVEC]) (0--3) THEN
  ARM_STEPS_TAC SI44_HPOST_EXEC (1--10) THEN SI44_HPOST_RED_TAC 0 11 THEN
  ARM_STEPS_TAC SI44_HPOST_EXEC (12--16) THEN SI44_HPOST_RED_TAC 1 17 THEN
  ARM_STEPS_TAC SI44_HPOST_EXEC [18] THEN SI44_HPOST_RED_TAC 2 19 THEN
  ARM_STEPS_TAC SI44_HPOST_EXEC [20] THEN SI44_HPOST_RED_TAC 3 21 THEN
  ARM_STEPS_TAC SI44_HPOST_EXEC (22--24) THEN SI44_HPOST_INV_TAC 0 25 THEN
  ARM_STEPS_TAC SI44_HPOST_EXEC (26--27) THEN SI44_HPOST_INV_TAC 1 28 THEN
  ARM_STEPS_TAC SI44_HPOST_EXEC (29--30) THEN SI44_HPOST_INV_TAC 2 31 THEN
  ARM_STEPS_TAC SI44_HPOST_EXEC (32--33) THEN SI44_HPOST_INV_TAC 3 34 THEN
  SI44_ASM_RW_TAC[GSYM SI44_YVL_EQ] THEN
  ARM_STEPS_TAC SI44_HPOST_EXEC (35--37) THEN SI44_HPOST_CADDQ_TAC 0 38 THEN
  ARM_STEPS_TAC SI44_HPOST_EXEC (39--45) THEN SI44_HPOST_CADDQ_TAC 1 46 THEN
  SI44_HPOST_CADDQ_TAC 2 47 THEN SI44_HPOST_CADDQ_TAC 3 48;;

let SI44_HPOST_SETUP_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    let ms,mcp = CONJ_PAIR th in SI44_HPOST_CALLEES ms mcp) THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(fp:int64) (guard:int64) (mf:int64) (mc:int64) (pc:num) (C:num).
      f_ev_hpost fp guard mf mc pc C:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `fp:int64`; `rho:num`; `RHO:num`; `MU:num`;
                       `att:num`; `C:num`; `guard:int64`; `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; fst SI44_HPOST_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SI44_ALIGNED16_32) THEN
  SI44_WEQ_TAC THEN
  FULL_INIT_TAC;;

(*** The four rows of w0 and of w1 packed joined into the vectors ***)

let SI44_ROWS_JOIN = prove
 (`!(f:(num->int32)->num->int32) (W:num->int32) (fp:int64) (s:armstate).
     (!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (4192 + 4 * i)))) s =
                      f (mld_poly_of W 0) i) /\
     (!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (5216 + 4 * i)))) s =
                      f (mld_poly_of W 1) i) /\
     (!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (6240 + 4 * i)))) s =
                      f (mld_poly_of W 2) i) /\
     (!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (7264 + 4 * i)))) s =
                      f (mld_poly_of W 3) i)
     ==> !i. i < 1024 ==> read (memory :> bytes32 (word_add fp (word (4192 + 4 * i)))) s =
                          mld_polyvec_map f W i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?k j. k < 4 /\ j < 256 /\ i = 256 * k + j` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC [`i DIV 256`; `i MOD 256`] THEN
    MP_TAC(SPECL [`i:num`; `256`] DIVISION) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MLD_POLYVEC_MAP_COEFF] THEN
  UNDISCH_TAC `k < 4` THEN SPEC_TAC(`k:num`,`k:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `4192 + 4 * (256 + j) = 5216 + 4 * j`;
              ARITH_RULE `4192 + 4 * (512 + j) = 6240 + 4 * j`;
              ARITH_RULE `4192 + 4 * (768 + j) = 7264 + 4 * j`; ADD_CLAUSES] THEN
  ASM_SIMP_TAC[]);;

let SI44_W1_JOIN = prove
 (`!(W:num->int32) (fp:int64) (s:armstate).
     (!j. j < 192 ==> read (memory :> bytes8 (word_add fp (word (8288 + j)))) s =
          mld_polyw1_pack_88 (mld_poly_decompose_hi_88 (mld_poly_of W 0)) j) /\
     (!j. j < 192 ==> read (memory :> bytes8 (word_add fp (word (8480 + j)))) s =
          mld_polyw1_pack_88 (mld_poly_decompose_hi_88 (mld_poly_of W 1)) j) /\
     (!j. j < 192 ==> read (memory :> bytes8 (word_add fp (word (8672 + j)))) s =
          mld_polyw1_pack_88 (mld_poly_decompose_hi_88 (mld_poly_of W 2)) j) /\
     (!j. j < 192 ==> read (memory :> bytes8 (word_add fp (word (8864 + j)))) s =
          mld_polyw1_pack_88 (mld_poly_decompose_hi_88 (mld_poly_of W 3)) j)
     ==> !j. j < 768 ==> read (memory :> bytes8 (word_add fp (word (8288 + j)))) s =
             mld_sign_w1 (mld_polyw1_pack_88 o mld_poly_decompose_hi_88) 192 W j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?k j. k < 4 /\ j < 192 /\ t = 192 * k + j` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC [`t DIV 192`; `t MOD 192`] THEN
    MP_TAC(SPECL [`t:num`; `192`] DIVISION) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[mld_sign_w1; MLD_POLYVEC_PACK_COEFF; o_THM] THEN
  UNDISCH_TAC `k < 4` THEN SPEC_TAC(`k:num`,`k:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `8288 + 192 + j = 8480 + j`;
              ARITH_RULE `8288 + 384 + j = 8672 + j`;
              ARITH_RULE `8288 + 576 + j = 8864 + j`; ADD_CLAUSES] THEN
  ASM_SIMP_TAC[]);;

let SI44_HPOST_DEC_TAC k n =
  (if k = 0 then ALL_TAC else SI44_NEST_TAC k (SI44_HPOLY SI44_W k)) THEN
  SI44_HCALL_TAC ("H_DEC" ^ string_of_int k) [SI44_FPK 0; `word_add fp (word 9056):int64`;
     SI44_HPOLY SI44_W k; `pc:num`] n THEN SI44_FLAT_TAC;;

let SI44_HPOST_W1PS_TAC k n =
  SI44_HCALL_TAC ("H_W1PS" ^ string_of_int k) [`fp:int64`;
     mk_comb(`mld_poly_decompose_hi_88`,SI44_HPOLY SI44_W k); `pc:num`] n;;

let SI44_W1N = mk_comb(`num_of_bytelist`,list_mk_comb(`list_of_seq:(num->byte)->num->byte list`,
                                                     [SI44_W1; `768`]));;

let SI44_CT_EQ = prove
 (mk_eq(list_mk_comb(`mld_shake256_byte`,[`64 + 768 + 0`;
    list_mk_comb(`(+):num->num->num`,[`MU:num`;
      list_mk_comb(`( * ):num->num->num`,[`2 EXP (8 * 64)`;
        list_mk_comb(`(+):num->num->num`,[SI44_W1N; `2 EXP (8 * 768) * 0`])])])]),
        SI44_CT),
  REWRITE_TAC[mld_sign_ctilde] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]);;

let SI44_HPOST_PART2_TAC =
  ARM_STEPS_TAC SI44_HPOST_EXEC [49] THEN
  SI44_HPOST_DEC_TAC 0 50 THEN SI44_HPOST_W1PS_TAC 0 51 THEN
  SI44_HPOST_DEC_TAC 1 52 THEN SI44_HPOST_W1PS_TAC 1 53 THEN
  SI44_HPOST_DEC_TAC 2 54 THEN SI44_HPOST_W1PS_TAC 2 55 THEN
  SI44_HPOST_DEC_TAC 3 56 THEN SI44_HPOST_W1PS_TAC 3 57 THEN
  (*** w1 packed as one string, and mld_H44 for c~ ***)
  MP_TAC(SPECL [SI44_W; `fp:int64`; `s57:armstate`] SI44_W1_JOIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`fp:int64`; `8288`; `768`; SI44_W1; `s57:armstate`]
               SIGN_READ_BYTES_OF_BYTES8_OFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ARM_STEPS_TAC SI44_HPOST_EXEC (58--60) THEN
  SUBGOAL_THEN `read (memory :> bytes(word 0,0)) s60 = 0` ASSUME_TAC THENL
   [REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL]; ALL_TAC] THEN
  SUBGOAL_THEN `nonoverlapping_modulo (2 EXP 64) (val (word_sub fp (word 544):int64),544) (0,0)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_MODULO_TRIVIAL THEN REWRITE_TAC[]; ALL_TAC] THEN
  SI44_HCALL_TAC "H_H44" [`read X0 s`; `32`; `read X2 s`; `64`; `read X4 s`; `768`;
     `word 0:int64`; `0`; `MU:num`; SI44_W1N; `0`; `guard:int64`; `pc:num`;
     `read SP s`; `read X30 s`] 61 THEN
  MLD_WRAP_EMPTY_REGIONS_TAC THEN
  SI44_ASM_RW_TAC[SI44_CT_EQ] THEN
  SI44_ASM_RW_TAC[ASSUME (mk_eq(SI44_CTN,`C:num`))] THEN
  ARM_STEPS_TAC SI44_HPOST_EXEC (62--65) THEN
  SI44_HCALL_TAC "H_CHAL" [`read X0 s`; `read X1 s`; `C:num`; `guard:int64`; `pc:num`;
     `read SP s`; `read X30 s`] 66 THEN
  ARM_STEPS_TAC SI44_HPOST_EXEC (67--68) THEN
  SI44_HCALL_TAC "H_NTT" [`read X0 s`; `mld_poly_challenge 39 32 C`;
     `pc:num`; `read SP s`; `read X30 s`] 69 THEN
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_forall c && can (find_term ((=) `mld_poly_challenge 39 32 C`)) c &&
       not(can (find_term (fun t -> is_const t && fst(dest_const t) = "ensures")) c)
    then REWRITE_RULE[GSYM mld_sign_cphat]
           (REWRITE_RULE[SYM(ASSUME (mk_eq(SI44_CTN,`C:num`)))] th)
    else th) THEN
  MP_TAC(SPECL [`mld_poly_decompose_lo_88`; SI44_W; `fp:int64`; `s69:armstate`]
               SI44_ROWS_JOIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SI44_END_TAC;;

let SI44_HPOST = prove
 (SI44_HPOST_STMT,
  SI44_HPOST_SETUP_TAC THEN SI44_HPOST_PART1_TAC THEN SI44_HPOST_PART2_TAC);;

(* ------------------------------------------------------------------------- *)
(* A column of the loop over y (YCOL), from loop3 with the column j in w27:  *)
(* y_j sampled (the inlined poly_uniform_gamma1, nonce 4 att + j) at         *)
(* fp + 9056 and transformed, then for each row i the entry (i,j) of the     *)
(* matrix sampled by poly_uniform from the seed rho || j || i at fp + 10112. *)
(* For j > 0 (SI44_YCOLJ, j = n + 1) its product with y^_j at fp + 832 is    *)
(* added to row i; for j = 0 (SI44_YCOL0) the entry is sampled into row i    *)
(* and multiplied in place. Row i then holds mld_lazy_acc rho i y^ j.        *)
(* ------------------------------------------------------------------------- *)

let SI44_SEED = prove
 (`!fp rho i j (s:armstate).
     read (memory :> bytes(word_add fp (word 10112),32)) s = rho /\
     read (memory :> bytes8 (word_add fp (word 10144))) s = word j /\
     read (memory :> bytes8 (word_add fp (word 10145))) s = word i /\
     i < 256 /\ j < 256
     ==> read (memory :> bytes(word_add fp (word 10112),34)) s = mld_matrix_seed rho i j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mld_matrix_seed] THEN
  REWRITE_TAC[ARITH_RULE `34 = 32 + 1 + 1`; READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  CONV_TAC(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[READ_MEMORY_BYTES_BYTES8] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC);;

let SI44_ACC_SUC = prove
 (`!rho i (v:num->int32) n.
     mld_lazy_acc rho i v (n + 1) =
     mld_poly_add (mld_lazy_acc rho i v n)
      (mld_poly_pointwise_montgomery (mld_poly_uniform (mld_matrix_seed rho i (n + 1)))
                                     (mld_poly_of v (n + 1)))`,
  REWRITE_TAC[GSYM ADD1; mld_lazy_acc; mld_matrix_entry]);;

let SI44_ACC_ROWS_N n = String.concat "" (map (fun k -> Printf.sprintf
  "(!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (%d + 4 * i)))) s =
                   mld_lazy_acc rho %d (%s) %s i)" (4192 + 1024 * k) k
  (string_of_term SI44_YH) n) (0--3));;

let SI44_YCOL_PRE =
 "read SP s = fp /\\
  read X22 s = word_add fp (word 10192) /\\ read X23 s = word_add fp (word 9056) /\\
  read X24 s = word 2 /\\
  read X25 s = word 18446744073701171199 /\\ read X26 s = word_add fp (word 10080) /\\
  read X28 s = word 252236767799803904 /\\
  read (memory :> bytes64 (word_add fp (word 264))) s = word_add fp (word 10513) /\\
  read (memory :> bytes64 (word_add fp (word 10080))) s = word_add fp (word 2080) /\\
  read (memory :> bytes16 (word_add fp (word 10088))) s = word (4 * att) /\\
  read (memory :> bytes128 (word_add fp (word 288))) s =
  word 0xffffff07ffffff06ffffff05ffffff04 /\\
  read (memory :> bytes128 (word_add fp (word 304))) s =
  word 0xffffff03ffffff02ffffff01ffffff00 /\\
  read (memory :> bytes (word_add fp (word 2080),64)) s = RHO /\\
  read (memory :> bytes (word_add fp (word 10112),32)) s = rho /\\
  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s = guard /\\
  read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
  read (memory :> bytes(ea,el)) s = ev";;

let SI44_YCOLJ_STMT = parse_term(
 "!mf mc ea el ev.
   memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
   ==> exists f_events.
        forall e fp rho RHO att n guard pc.
         aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
         aligned 32 fp /\\ att < 16382 /\\ n < 3 /\\ mld_matrix_terminates 4 4 rho /\\
         ALL (nonoverlapping (word_sub fp (word 1472),12672))
             [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8); (guard,8);
              (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
         ==> ensures arm
              (\\s. aligned_bytes_loaded s (word pc)
                     mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                   read PC s = word (pc + mldsa44_signature_internal_loop3) /\\
                   read X27 s = word (n + 1) /\\\n" ^ SI44_YCOL_PRE ^ " /\\\n" ^
  String.concat " /\\\n" (map (fun k -> Printf.sprintf
  "(!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (%d + 4 * i)))) s =
                   mld_lazy_acc rho %d (%s) n i)" (4192 + 1024 * k) k
  (string_of_term SI44_YH)) (0--3)) ^ " /\\
                   read events s = e)
              (\\s. read PC s = (if n + 2 < 4 then word (pc + mldsa44_signature_internal_loop3)
                                else word (pc + mldsa44_signature_internal_loop3_exit)) /\\
                   read SP s = fp /\\ read X27 s = word (n + 2) /\\
                   read X19 s = word_add fp (word 4192) /\\
                   read X22 s = word_add fp (word 10192) /\\
                   read X26 s = word_add fp (word 10080) /\\\n" ^
  String.concat " /\\\n" (map (fun k -> Printf.sprintf
  "(!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (%d + 4 * i)))) s =
                   mld_lazy_acc rho %d (%s) (n + 1) i)" (4192 + 1024 * k) k
  (string_of_term SI44_YH)) (0--3)) ^ " /\\
                   (exists e2.
                      read events s = APPEND e2 e /\\
                      e2 = f_events fp rho n guard mf mc pc /\\
                      memaccess_inbounds e2
                       [word_sub fp (word 1472),12672;
                        word(pc + got_stack_chk_guard),8; guard,8;
                        word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                        word(pc + rodata_mld_KeccakF_RoundConstants),192;
                        word(pc + rodata_mld_zetas),1024;
                        word(pc + mldsa44_signature_internal_consts),128]
                       [word_sub fp (word 1472),12672]))
              (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [X18; X19; X20; X21; X22; X26; X27; X30] ,,
               MAYCHANGE [memory :> bytes(word_sub fp (word 1472),1472);
                          memory :> bytes(word_add fp (word 832),1024);
                          memory :> bytes(word_add fp (word 4192),4096);
                          memory :> bytes(word_add fp (word 9056),1024);
                          memory :> bytes(word_add fp (word 10144),2);
                          memory :> bytes(word_add fp (word 10192),984)])");;

let SI44_YCOL_EXEC = SI44_EXEC_RANGE "join3" "loop3_exit";;

let SI44_ZX8 = prove
 (`!k. k < 256 ==> word_zx (word k:int64):byte = word k`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `k MOD 256 = k /\ k MOD 18446744073709551616 = k` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_REWRITE_TAC[]]);;

let SI44_COLNZ = prove
 (`!n. n < 3 ==> ~(val (word_zx (word (n + 1):int64):int32) = 0)`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

(*** The seed rho || j || i of entry (i,j) and the termination of its     ***)
(*** sampling, before a call of poly_uniform at state st                  ***)

let SI44_PU_PRE_TAC i jt st =
  MP_TAC(SPECL [`fp:int64`; `rho:num`; mk_small_numeral i; jt; st] SI44_SEED) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `n + 1 < 256` ASSUME_TAC THENL
     [UNDISCH_TAC `n < 3` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SI44_ZX_BYTE; SI44_ZX8] THEN UNDISCH_TAC `n < 3` THEN ARITH_TAC;
    DISCH_TAC] THEN
  FIRST_ASSUM(fun th -> if can (term_match [] `mld_matrix_terminates 4 4 r`) (concl th) then
    MP_TAC(SPECL [mk_small_numeral i; jt] (REWRITE_RULE[mld_matrix_terminates] th)) THEN
    ANTS_TAC THENL [UNDISCH_TAC `n < 3` THEN ARITH_TAC; DISCH_TAC] else NO_TAC);;

let SI44_YCOL_ALLOWED = [`fp:int64`; `rho:num`; `n:num`; `guard:int64`; `mf:int64`;
                         `mc:int64`; `pc:num`];;

let SI44_YCOL_CALL_TAC name ilist k =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc SI44_YCOL_EXEC name
    ilist SI44_YCOL_ALLOWED k;;

let SI44_YY k = mk_comb(mk_comb(`mld_poly_of`,
  `mld_sign_y mld_poly_uniform_gamma1_17 RHO (4 * att)`),k);;
let SI44_YHK k = mk_comb(mk_comb(`mld_poly_of`,SI44_YH),k);;
let SI44_ACC i nt = list_mk_comb(`mld_lazy_acc`,[`rho:num`; mk_small_numeral i; SI44_YH; nt]);;
let SI44_ENT i jt = mk_comb(`mld_poly_uniform`,
  list_mk_comb(`mld_matrix_seed`,[`rho:num`; mk_small_numeral i; jt]));;
let SI44_PWT i jt = list_mk_comb(`mld_poly_pointwise_montgomery`,[SI44_ENT i jt; SI44_YHK jt]);;

(*** The callees of a column ***)

let SI44_YCOL_CALLEES th =
  ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP SI44_G1_Y th) "H_G1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    (MATCH_MP MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL th)
    "H_PU" THEN
  MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
   ([MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_NTT"] @
    map (fun k -> SI44_RIT_LK SI44_PWM ("loop" ^ string_of_int (6 + k)),
                  "H_PWM" ^ string_of_int k) (0--3) @
    map (fun k -> el k SI44_ADDS, "H_ADD" ^ string_of_int k) (0--3) @
    map (fun k -> SI44_RIT_LK SI44_PWM ("loop" ^ string_of_int (10 + k)),
                  "H_PWMZ" ^ string_of_int k) (0--3));;

(*** y_j (index jt, nonce 4 att + jt) and its NTT, up to the branch on j ***)

let SI44_YCOL_Y_TAC jt =
  ARM_STEPS_TAC SI44_YCOL_EXEC (1--5) THEN
  SUBGOAL_THEN `4 * att < 65536` ASSUME_TAC THENL
   [UNDISCH_TAC `att < 16382` THEN ARITH_TAC; ALL_TAC] THEN
  SI44_ASM_RW_TAC[MP (SPEC `4 * att` SI44_ZX16) (ASSUME `4 * att < 65536`)] THEN
  MAP_EVERY ASSUME_TAC SI44_FR_EQS THEN
  SI44_YCOL_CALL_TAC "H_G1" [`word_add fp (word 2080):int64`; `RHO:num`; `4 * att`; jt;
    `word_sub fp (word 240):int64`; `pc:num`] 6 THEN
  SI44_ASM_RW_TAC SI44_FR_EQS THEN
  MLD_LAZY_REPOLY_TAC
    (list_mk_comb(`mld_poly_uniform_gamma1_17`,
      [`RHO:num`; mk_comb(`word:num->int16`,mk_binop `(+):num->num->num` `4 * att` jt)]))
    (SI44_YY jt) [mld_sign_y; MLD_POLY_OF_POLYVEC] THEN
  ARM_STEPS_TAC SI44_YCOL_EXEC (7--21) THEN
  SI44_YCOL_CALL_TAC "H_NTT" [`read X0 s`; SI44_YY jt; `pc:num`; `read SP s`;
                              `read X30 s`] 22 THEN
  MLD_LAZY_REPOLY_TAC (mk_comb(`mld_poly_ntt`,SI44_YY jt)) (SI44_YHK jt)
    [MLD_POLY_OF_POLYVEC_MAP] THEN
  ARM_STEPS_TAC SI44_YCOL_EXEC (23--26) THEN
  SI44_ASM_RW_TAC[MP (SI44_ORR_THM 9056 8) (ASSUME `aligned 32 (fp:int64)`)] THEN
  ARM_STEPS_TAC SI44_YCOL_EXEC [27];;

(*** Row i of a column j > 0, the call of poly_uniform being step n0 ***)

let SI44_YCOLJ_ROW_TAC i n0 =
  let jt = `n + 1` in
  (if i = 0 then ALL_TAC else ARM_STEPS_TAC SI44_YCOL_EXEC [n0 - 1]) THEN
  SI44_PU_PRE_TAC i jt (mk_var("s"^string_of_int (n0-1),`:armstate`)) THEN
  SI44_YCOL_CALL_TAC "H_PU" [`read X0 s`; `read X1 s`;
    list_mk_comb(`mld_matrix_seed`,[`rho:num`; mk_small_numeral i; jt]);
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] n0 THEN
  ARM_STEPS_TAC SI44_YCOL_EXEC [n0 + 1] THEN
  SI44_YCOL_CALL_TAC ("H_PWM" ^ string_of_int i)
    [`word_add fp (word 832):int64`; `word_add fp (word 9056):int64`;
     SI44_ENT i jt; SI44_YHK jt; `pc:num`] (n0 + 2) THEN
  SI44_YCOL_CALL_TAC ("H_ADD" ^ string_of_int i)
    ([`fp:int64`; SI44_ACC i `n:num`; SI44_PWT i jt] @
     (if i < 3 then [jt] else []) @ [`pc:num`]) (n0 + 3) THEN
  SI44_ASM_RW_TAC[GSYM SI44_ACC_SUC];;

let SI44_COLINC = prove
 (`!n. n < 3
       ==> word_zx (word_add (word_zx (word (n + 1):int64):int32) (word 1)):int64 =
           word (n + 2)`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV);;

let SI44_COLTEST = prove
 (`!n. n < 3
       ==> (val (word_sub (word_zx (word (n + 2):int64):int32) (word 4)) = 0 <=>
            ~(n + 2 < 4))`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let SI44_YCOLJ = prove
 (SI44_YCOLJ_STMT,
  REPEAT GEN_TAC THEN DISCH_THEN SI44_YCOL_CALLEES THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(fp:int64) (rho:num) (n:num) (guard:int64) (mf:int64) (mc:int64) (pc:num).
      if n + 2 < 4 then f_ev_mid fp rho n guard mf mc pc
      else f_ev_last fp rho n guard mf mc pc:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `fp:int64`; `rho:num`; `RHO:num`; `att:num`;
                       `n:num`; `guard:int64`; `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; fst SI44_YCOL_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SI44_ALIGNED16_32) THEN
  FULL_INIT_TAC THEN SI44_YCOL_Y_TAC `n + 1` THEN
  SI44_ASM_RW_TAC[MP (SPEC `n:num` SI44_COLNZ) (ASSUME `n < 3`)] THEN
  ARM_STEPS_TAC SI44_YCOL_EXEC (28--33) THEN
  SI44_YCOLJ_ROW_TAC 0 34 THEN SI44_YCOLJ_ROW_TAC 1 39 THEN
  SI44_YCOLJ_ROW_TAC 2 44 THEN SI44_YCOLJ_ROW_TAC 3 49 THEN
  ARM_STEPS_TAC SI44_YCOL_EXEC (53--56) THEN
  SI44_ASM_RW_TAC[MP (SPEC `n:num` SI44_COLINC) (ASSUME `n < 3`)] THEN
  SI44_ASM_RW_TAC[MP (SPEC `n:num` SI44_COLTEST) (ASSUME `n < 3`)] THEN
  SI44_CASES_TAC `n + 2 < 4` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SI44_END_TAC);;

(*** The column j = 0 ***)

let SI44_YCOL0_STMT = parse_term(
 "!mf mc ea el ev.
   memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
   ==> exists f_events.
        forall e fp rho RHO att guard pc.
         aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
         aligned 32 fp /\\ att < 16382 /\\ mld_matrix_terminates 4 4 rho /\\
         ALL (nonoverlapping (word_sub fp (word 1472),12672))
             [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8); (guard,8);
              (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
         ==> ensures arm
              (\\s. aligned_bytes_loaded s (word pc)
                     mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                   read PC s = word (pc + mldsa44_signature_internal_loop3) /\\
                   read X27 s = word 0 /\\\n" ^ SI44_YCOL_PRE ^ " /\\
                   read events s = e)
              (\\s. read PC s = word (pc + mldsa44_signature_internal_loop3) /\\
                   read SP s = fp /\\ read X27 s = word 1 /\\
                   read X19 s = word_add fp (word 4192) /\\
                   read X22 s = word_add fp (word 10192) /\\
                   read X26 s = word_add fp (word 10080) /\\\n" ^
  String.concat " /\\\n" (map (fun k -> Printf.sprintf
  "(!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (%d + 4 * i)))) s =
                   mld_lazy_acc rho %d (%s) 0 i)" (4192 + 1024 * k) k
  (string_of_term SI44_YH)) (0--3)) ^ " /\\
                   (exists e2.
                      read events s = APPEND e2 e /\\
                      e2 = f_events fp rho guard mf mc pc /\\
                      memaccess_inbounds e2
                       [word_sub fp (word 1472),12672;
                        word(pc + got_stack_chk_guard),8; guard,8;
                        word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                        word(pc + rodata_mld_KeccakF_RoundConstants),192;
                        word(pc + rodata_mld_zetas),1024;
                        word(pc + mldsa44_signature_internal_consts),128]
                       [word_sub fp (word 1472),12672]))
              (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [X18; X19; X20; X21; X22; X26; X27; X30] ,,
               MAYCHANGE [memory :> bytes(word_sub fp (word 1472),1472);
                          memory :> bytes(word_add fp (word 832),1024);
                          memory :> bytes(word_add fp (word 4192),4096);
                          memory :> bytes(word_add fp (word 9056),1024);
                          memory :> bytes(word_add fp (word 10144),2);
                          memory :> bytes(word_add fp (word 10192),984)])");;

(*** The seed from the 16-bit index j + 256 i stored by strh ***)

let SI44_SEED16 = prove
 (`!fp rho i (s:armstate).
     read (memory :> bytes(word_add fp (word 10112),32)) s = rho /\
     read (memory :> bytes16 (word_add fp (word 10144))) s = word (256 * i) /\
     i < 256
     ==> read (memory :> bytes(word_add fp (word 10112),34)) s = mld_matrix_seed rho i 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mld_matrix_seed] THEN
  REWRITE_TAC[ARITH_RULE `34 = 32 + 2`; READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  CONV_TAC(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `read (memory :> bytes(word_add fp (word 10144),2)) s = val(word (256 * i):int16)`
   SUBST1_TAC THENL
   [FIRST_X_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes16 a) s = x`) (concl th)
      then REWRITE_TAC[GSYM th] else NO_TAC) THEN
    REWRITE_TAC[BYTES16_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES; DIMINDEX_16] THEN
    CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[VAL_WORD; DIMINDEX_16] THEN
    SUBGOAL_THEN `(256 * i) MOD 2 EXP 16 = 256 * i` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ARITH_TAC]]);;

let SI44_PU0_PRE_TAC i st =
  MP_TAC(SPECL [`fp:int64`; `rho:num`; mk_small_numeral i; st] SI44_SEED16) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    TRY(FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes16 a) s = x`) (concl th)
                              then REWRITE_TAC[th] THEN CONV_TAC WORD_REDUCE_CONV else NO_TAC));
    DISCH_TAC] THEN
  FIRST_ASSUM(fun th -> if can (term_match [] `mld_matrix_terminates 4 4 r`) (concl th) then
    MP_TAC(SPECL [mk_small_numeral i; `0`] (REWRITE_RULE[mld_matrix_terminates] th)) THEN
    ANTS_TAC THENL [ARITH_TAC; DISCH_TAC] else NO_TAC);;

let SI44_ACC0 = prove
 (`!rho i (v:num->int32).
     mld_lazy_acc rho i v 0 =
     mld_poly_pointwise_montgomery (mld_poly_uniform (mld_matrix_seed rho i 0))
                                   (mld_poly_of v 0)`,
  REWRITE_TAC[mld_lazy_acc; mld_matrix_entry]);;

(*** Row i of the column j = 0, the call of poly_uniform being step n0 ***)

let SI44_YCOL0_ROW_TAC i n0 =
  (if i = 0 then ALL_TAC else
     ARM_STEPS_TAC SI44_YCOL_EXEC ((n0 - 6)--(n0 - 1)) THEN
     SI44_PU0_PRE_TAC i (mk_var("s"^string_of_int (n0-1),`:armstate`))) THEN
  SI44_YCOL_CALL_TAC "H_PU" [`read X0 s`; `read X1 s`;
    list_mk_comb(`mld_matrix_seed`,[`rho:num`; mk_small_numeral i; `0`]);
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] n0 THEN
  (if i = 0 then ARM_STEPS_TAC SI44_YCOL_EXEC ((n0+1)--(n0+5)) THEN
     SI44_ASM_RW_TAC[MP (SI44_ORR_THM 9056 8) (ASSUME `aligned 32 (fp:int64)`);
                     MP (SI44_ORR_THM 4192 8) (ASSUME `aligned 32 (fp:int64)`)]
   else ARM_STEPS_TAC SI44_YCOL_EXEC ((n0+1)--(n0+3)) THEN
     SI44_ASM_RW_TAC[MP (SI44_ORR_THM 9056 8) (ASSUME `aligned 32 (fp:int64)`)]) THEN
  SI44_YCOL_CALL_TAC ("H_PWMZ" ^ string_of_int i)
    [SI44_FPK i; `word_add fp (word 9056):int64`; SI44_ENT i `0`; SI44_YHK `0`; `pc:num`]
    (if i = 0 then n0 + 6 else n0 + 4) THEN
  SI44_ASM_RW_TAC[GSYM SI44_ACC0];;

let SI44_YCOL0 = prove
 (SI44_YCOL0_STMT,
  REPEAT GEN_TAC THEN DISCH_THEN SI44_YCOL_CALLEES THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(fp:int64) (rho:num) (guard:int64) (mf:int64) (mc:int64) (pc:num).
      f_ev_col0 fp rho guard mf mc pc:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `fp:int64`; `rho:num`; `RHO:num`; `att:num`;
                       `guard:int64`; `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; fst SI44_YCOL_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SI44_ALIGNED16_32) THEN
  FULL_INIT_TAC THEN SI44_YCOL_Y_TAC `0` THEN
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read PC s = x`) (concl th) then
     CONV_RULE(DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV) th else th) THEN
  ARM_STEPS_TAC SI44_YCOL_EXEC (28--33) THEN SI44_PU0_PRE_TAC 0 `s33:armstate` THEN
  SI44_YCOL0_ROW_TAC 0 34 THEN SI44_YCOL0_ROW_TAC 1 47 THEN
  SI44_YCOL0_ROW_TAC 2 58 THEN SI44_YCOL0_ROW_TAC 3 69 THEN
  ARM_STEPS_TAC SI44_YCOL_EXEC (74--77) THEN
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read PC s = x`) (concl th) ||
                              can (term_match [] `read X27 s = x`) (concl th) then
     CONV_RULE(DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV) th else th) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SI44_END_TAC);;

(* ------------------------------------------------------------------------- *)
(* The start of an attempt (HEAD), from loop2 with its number att in w9: att *)
(* saved at fp + 204, kappa = 4 att (16 bits) and the pointer to rho'' in    *)
(* the structure at fp + 10080, rho copied from fp + 1856 to the seed of the *)
(* matrix at fp + 10112, then the four columns of the product with the       *)
(* matrix (YCOL0, YCOLJ for n = 0, 1, 2) and HPOST, to after the NTT of the  *)
(* challenge, as gcc's SIGN44_HEAD.                                          *)
(* ------------------------------------------------------------------------- *)

let SI44_HEAD_PRE =
 "read SP s = fp /\\
  read X22 s = word_add fp (word 10192) /\\ read X23 s = word_add fp (word 9056) /\\
  read X24 s = word 2 /\\
  read X25 s = word 18446744073701171199 /\\ read X26 s = word_add fp (word 10080) /\\
  read X28 s = word 252236767799803904 /\\
  read (memory :> bytes64 (word_add fp (word 152))) s = word_add fp (word 1856) /\\
  read (memory :> bytes64 (word_add fp (word 160))) s = word_add fp (word 2080) /\\
  read (memory :> bytes64 (word_add fp (word 264))) s = word_add fp (word 10513) /\\
  read (memory :> bytes128 (word_add fp (word 240))) s =
  word 339618401959998730991157055895298383871 /\\
  read (memory :> bytes128 (word_add fp (word 288))) s =
  word 0xffffff07ffffff06ffffff05ffffff04 /\\
  read (memory :> bytes128 (word_add fp (word 304))) s =
  word 0xffffff03ffffff02ffffff01ffffff00 /\\\n" ^
  SI44_SLOT_FACTS [56,9008; 64,8960; 72,8912; 80,8816; 88,8768; 96,8720; 104,8624;
                   112,8576; 120,8528; 128,8432; 136,8384; 144,8336;
                   168,8864; 176,8672; 184,8480] ^
 "read (memory :> bytes (word_add fp (word 1856),32)) s = rho /\\
  read (memory :> bytes (word_add fp (word 2016),64)) s = MU /\\
  read (memory :> bytes (word_add fp (word 2080),64)) s = RHO /\\
  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s = guard /\\
  read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
  read (memory :> bytes(ea,el)) s = ev";;

let SI44_HEAD_STMT = parse_term(
 "!mf mc ea el ev.
   memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
   ==> exists f_events.
        forall e fp att rho RHO MU C guard pc.
         aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
         aligned 32 fp /\\ att < 16382 /\\ mld_matrix_terminates 4 4 rho /\\
         " ^ string_of_term SI44_CTN ^ " = C /\\
         mld_poly_challenge_terminates 39 32 C /\\
         ALL (nonoverlapping (word_sub fp (word 1472),12672))
             [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8); (guard,8);
              (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
         ==> ensures arm
              (\\s. aligned_bytes_loaded s (word pc)
                     mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                   read PC s = word (pc + mldsa44_signature_internal_loop2) /\\
                   read X9 s = word att /\\\n" ^ SI44_HEAD_PRE ^ " /\\
                   read events s = e)
              (\\s. read PC s = word (pc + mldsa44_signature_internal_after_mldsa_poly_ntt_2) /\\
                   read SP s = fp /\\
                   read X20 s = word_add fp (word 2144) /\\
                   read X22 s = word_add fp (word 10192) /\\
                   read X26 s = word_add fp (word 10080) /\\
                   read (memory :> bytes32 (word_add fp (word 204))) s = word att /\\
                   read (memory :> bytes64 (word_add fp (word 10080))) s = word_add fp (word 2080) /\\
                   read (memory :> bytes16 (word_add fp (word 10088))) s = word (4 * att) /\\
                   (!i. i < 1024 ==> read (memory :> bytes32 (word_add fp (word (4192 + 4 * i)))) s =
                                     mld_polyvec_map mld_poly_decompose_lo_88 (" ^
                                       string_of_term SI44_W ^ ") i) /\\
                   (!j. j < 768 ==> read (memory :> bytes8 (word_add fp (word (8288 + j)))) s =
                                    " ^ string_of_term SI44_W1 ^ " j) /\\
                   read (memory :> bytes (word_add fp (word 10112),32)) s = C /\\
                   (!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (3168 + 4 * i)))) s =
                                    mld_sign_cphat 39 32 (" ^ string_of_term SI44_CT ^ ") i) /\\
                   (exists e2.
                      read events s = APPEND e2 e /\\
                      e2 = f_events fp rho C guard mf mc pc /\\
                      memaccess_inbounds e2
                       [word_sub fp (word 1472),12672;
                        word(pc + got_stack_chk_guard),8; guard,8;
                        word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                        word(pc + rodata_mld_KeccakF_RoundConstants),192;
                        word(pc + rodata_mld_zetas),1024;
                        word(pc + mldsa44_signature_internal_consts),128]
                       [word_sub fp (word 1472),12672]))
              (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [X18; X19; X20; X21; X22; X26; X27; X30] ,,
               MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
               MAYCHANGE [memory :> bytes(word_sub fp (word 1472),1472);
                          memory :> bytes(word_add fp (word 204),4);
                          memory :> bytes(word_add fp (word 528),208);
                          memory :> bytes(word_add fp (word 832),1024);
                          memory :> bytes(word_add fp (word 3168),1024);
                          memory :> bytes(word_add fp (word 4192),4096);
                          memory :> bytes(word_add fp (word 8288),768);
                          memory :> bytes(word_add fp (word 9056),1024);
                          memory :> bytes(word_add fp (word 10080),16);
                          memory :> bytes(word_add fp (word 10112),64);
                          memory :> bytes(word_add fp (word 10192),984)])");;

let SI44_HEAD_EXEC = SI44_EXEC_RANGE "loop2" "after_mldsa_poly_ntt_2";;

let SI44_HEAD_ALLOWED = [`fp:int64`; `rho:num`; `C:num`; `guard:int64`; `mf:int64`;
                         `mc:int64`; `pc:num`];;

let SI44_HEAD_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc SI44_HEAD_EXEC name
    ilist SI44_HEAD_ALLOWED n;;

(*** att as str w9 stores it ***)

let SI44_ZX32 = prove
 (`!n. word_zx (word n:int64):int32 = word n`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

(*** kappa = 4 att as strh stores it (lsl w8, w9, #2) ***)

let SI44_KAPPA_TAC =
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes16 (word_add fp (word 10088))) s = x`)
           (concl th) then
      let r = rhs(concl th) in
      let eq = prove(mk_imp(`att < 16382`, mk_eq(r, `word (4 * att):int16`)),
        DISCH_TAC THEN
        REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_SHL; VAL_WORD; DIMINDEX_16;
                    DIMINDEX_32; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        SUBGOAL_THEN `att MOD 4294967296 = att` SUBST1_TAC THENL
         [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; REFL_TAC]) in
      ASSUME_TAC(TRANS th (MP eq (ASSUME `att < 16382`)))
    else NO_TAC);;

(*** The facts of a column after its call: its numerals evaluated (the PC ***)
(*** test, the column in x27 and the count of the sums in the rows)       ***)

let SI44_HEAD_NUM_TAC =
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if can (find_term (fun t -> is_const t && fst(dest_const t) = "ensures")) c then th
    else if can (term_match [] `read PC s = x`) c || can (term_match [] `read X27 s = x`) c ||
       (is_forall c &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mld_lazy_acc")) c)
    then CONV_RULE(NUM_REDUCE_CONV THENC REWRITE_CONV[]) th else th);;

let SI44_HEAD_COL_TAC n k =
  SI44_REG_FORM_TAC "X27" (k - 1) (subst [mk_small_numeral n,`n:num`] `word (n + 1):int64`) THEN
  SI44_HEAD_CALL_TAC "H_YCJ" [`fp:int64`; `rho:num`; `RHO:num`; `att:num`; mk_small_numeral n;
                              `guard:int64`; `pc:num`] k THEN
  SI44_HEAD_NUM_TAC;;

let SI44_HEAD = prove
 (SI44_HEAD_STMT,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
     [MP (SPEC_ALL SI44_YCOL0) th,"H_YC0"; MP (SPEC_ALL SI44_YCOLJ) th,"H_YCJ";
      MP (SPEC_ALL SI44_HPOST) th,"H_HP"]) THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(fp:int64) (rho:num) (C:num) (guard:int64) (mf:int64) (mc:int64) (pc:num).
      f_ev_head fp rho C guard mf mc pc:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `fp:int64`; `att:num`; `rho:num`; `RHO:num`;
                       `MU:num`; `C:num`; `guard:int64`; `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; fst SI44_HEAD_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SI44_ALIGNED16_32) THEN
  FULL_INIT_TAC THEN
  (*** the head of loop2: att, kappa, the pointer to rho'' and rho ***)
  MAP_EVERY (fun n ->
    MP_TAC(SPECL [`word_add fp (word 1856):int64`; `32`; `rho:num`; mk_small_numeral n;
                  `s0:armstate`] SIGN_BYTES128_OF_BYTES) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC) [0;1] THEN
  ARM_STEPS_TAC SI44_HEAD_EXEC (1--10) THEN
  SI44_KAPPA_TAC THEN SI44_ASM_RW_TAC[SI44_ZX32] THEN
  SUBGOAL_THEN `rho < 2 EXP (8 * 32)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if can (term_match []
       `read (memory :> bytes (word_add fp (word 1856),32)) s0 = rho`) (concl th)
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[READ_BYTES_BOUND; READ_COMPONENT_COMPOSE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`word_add fp (word 10112):int64`; `rho:num`; `2`; `s10:armstate`]
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
  (*** the four columns of A y and HPOST ***)
  SI44_HEAD_CALL_TAC "H_YC0" [`fp:int64`; `rho:num`; `RHO:num`; `att:num`; `guard:int64`;
                              `pc:num`] 11 THEN
  SI44_HEAD_COL_TAC 0 12 THEN SI44_HEAD_COL_TAC 1 13 THEN SI44_HEAD_COL_TAC 2 14 THEN
  SI44_HEAD_CALL_TAC "H_HP" [`fp:int64`; `rho:num`; `RHO:num`; `MU:num`; `att:num`; `C:num`;
                             `guard:int64`; `pc:num`] 15 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SI44_END_TAC);;

(* ------------------------------------------------------------------------- *)
(* A whole attempt (ATT), from loop2 with its number att in w9 to the exit   *)
(* of the cleanup: to loop2_exit2 on success (r = 13), else to loop2 with    *)
(* att + 1 in w9 or, after the last attempt, to loop2_exit1. By cases on the *)
(* result r of mld_sign_attempt_declass, as gcc's SIGN44_ATT: r < 4 (z_r     *)
(* fails: ZPRE, then ZIT and join10), 4 <= r < 12 (check r - 4 of the rows   *)
(* fails: ZPRE, RPRE, then RIT and join10), 12 (too many hints) and 13       *)
(* (success), both through TAIL; then CLEAN from join11.                     *)
(* ------------------------------------------------------------------------- *)

let SI44_ATT_CPH = `mld_poly_ntt (mld_poly_challenge 39 32 C)`;;
let SI44_ATT_W = SI44_W;;
let SI44_ATT_R0 = list_mk_comb(`mld_sign_r0`,
  [`mld_poly_decompose_lo_88`; SI44_ATT_W; SI44_S2H; SI44_ATT_CPH]);;
let SI44_ATT_CT0 = list_mk_comb(`mld_sign_ct0`,[SI44_T0H; SI44_ATT_CPH]);;
let SI44_SIGATT = list_mk_comb(
 `mld_sign_attempt_sig 4 4 32 39 mld_poly_uniform_gamma1_17 mld_polyz_pack_17
   576 (mld_polyw1_pack_88 o mld_poly_decompose_hi_88) 192
   mld_poly_decompose_lo_88 mld_polyvec_make_hint_88 80`,
  [`mld_polyvec_matrix_expand 4 rho`; SI44_S1H; SI44_S2H; SI44_T0H; `MU:num`; `RHO:num`;
   `4 * att`]);;

let SI44_ATT_STMT = parse_term(
 "!mf mc ea el ev.
   memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
   ==> exists f_events.
        forall e sig sk skb fp rho MU RHO att C r x b guard pc.
         aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
         aligned 32 fp /\\ att < 16382 /\\ mld_matrix_terminates 4 4 rho /\\
         mld_sign_attempt_declass 4 4 32 39 mld_poly_uniform_gamma1_17
          130994 95154 95232 (mld_polyw1_pack_88 o mld_poly_decompose_hi_88)
          192 mld_poly_decompose_lo_88 mld_polyvec_make_hint_88 80
          (mld_polyvec_matrix_expand 4 rho) (" ^ string_of_term SI44_S1H ^ ")
          (" ^ string_of_term SI44_S2H ^ ") (" ^ string_of_term SI44_T0H ^ ")
          MU RHO (4 * att) = (C,r,x,b) /\\
         mld_poly_challenge_terminates 39 32 C /\\
         nonoverlapping (sig,2420) (word_sub fp (word 1472),12672) /\\
         ALL (nonoverlapping (word_sub fp (word 1472),12672))
             [(sk,2560); (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
              (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\\
         ALL (nonoverlapping (sig,2420))
             [(sk,2560); (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
              (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
         ==> ensures arm
              (\\s. aligned_bytes_loaded s (word pc)
                     mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                   read PC s = word (pc + mldsa44_signature_internal_loop2) /\\
                   read X9 s = word att /\\\n" ^ SI44_HEAD_PRE ^ " /\\\n" ^
  SI44_SLOT_FACTS [24,7264; 32,6240; 40,5216; 232,3168] ^
 "                 read (memory :> bytes64 (word_add fp (word 192))) s = sig /\\
                   read (memory :> bytes64 (word_add fp (word 48))) s =
                   word_add sig (word 2336) /\\
                   read (memory :> bytes64 (word_add fp (word 208))) s = word_add fp (word 3176) /\\
                   read (memory :> bytes64 (word_add fp (word 736))) s = word_add sk (word 512) /\\
                   read (memory :> bytes64 (word_add fp (word 768))) s = word_add sk (word 896) /\\
                   read (memory :> bytes64 (word_add fp (word 800))) s = word_add sk (word 128) /\\
                   (!i. i < 2560 ==> read (memory :> bytes8 (word_add sk (word i))) s = skb i) /\\
                   read events s = e)
              (\\s. read PC s =
                   (if r = 13 then word (pc + mldsa44_signature_internal_loop2_exit2)
                    else if att + 1 < 16382 then word (pc + mldsa44_signature_internal_loop2)
                    else word (pc + mldsa44_signature_internal_loop2_exit1)) /\\
                   read SP s = fp /\\
                   read X22 s = word_add fp (word 10192) /\\
                   read X26 s = word_add fp (word 10080) /\\
                   (~(r = 13) ==> read X9 s = word (att + 1)) /\\
                   read (memory :> bytes64(word(pc + got_stack_chk_guard))) s = guard /\\
                   read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                   read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                   read (memory :> bytes(ea,el)) s = ev /\\
                   (r = 13
                    ==> !t. t < 2420
                            ==> read (memory :> bytes8 (word_add sig (word t))) s =
                                (" ^ string_of_term SI44_SIGATT ^ ") t) /\\
                   (exists e2.
                      read events s = APPEND e2 e /\\
                      e2 = f_events sig sk fp rho att C r x b guard mf mc pc /\\
                      memaccess_inbounds e2
                       [sig,2420; sk,2560; word_sub fp (word 1472),12672;
                        word(pc + got_stack_chk_guard),8; guard,8;
                        word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                        word(pc + rodata_mld_KeccakF_RoundConstants),192;
                        word(pc + rodata_mld_zetas),1024;
                        word(pc + mldsa44_signature_internal_consts),128]
                       [sig,2420; word_sub fp (word 1472),12672]))
              (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [X18; X19; X20; X21; X22; X26; X27; X30] ,,
               MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
               MAYCHANGE [memory :> bytes(sig,2420);
                          memory :> bytes(word_sub fp (word 1472),1472);
                          memory :> bytes(word_add fp (word 204),4);
                          memory :> bytes(word_add fp (word 216),16);
                          memory :> bytes(word_add fp (word 272),16);
                          memory :> bytes(word_add fp (word 320),416);
                          memory :> bytes(word_add fp (word 832),1024);
                          memory :> bytes(word_add fp (word 2144),1024);
                          memory :> bytes(word_add fp (word 3168),1024);
                          memory :> bytes(word_add fp (word 4192),4096);
                          memory :> bytes(word_add fp (word 8288),768);
                          memory :> bytes(word_add fp (word 9056),1024);
                          memory :> bytes(word_add fp (word 10080),16);
                          memory :> bytes(word_add fp (word 10112),64);
                          memory :> bytes(word_add fp (word 10192),984)])");;

let SI44_ATT_EXEC = MLDSA_NATIVE_SIGNATURE_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;

let SI44_ATT_ALLOWED =
  [`sig:int64`; `sk:int64`; `fp:int64`; `rho:num`; `att:num`; `C:num`; `r:num`;
   `x:num->int32`; `b:num->byte`; `guard:int64`; `mf:int64`; `mc:int64`; `pc:num`];;

let SI44_ATT_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc SI44_ATT_EXEC name
    ilist SI44_ATT_ALLOWED n;;

let SI44_ATT_MID = parse_term(
 "\\s. read SP s = fp /\\
      read X19 s = (if r = 13 then word 1 else word 0) /\\
      read X22 s = word_add fp (word 10192) /\\
      read X26 s = word_add fp (word 10080) /\\
      read (memory :> bytes32 (word_add fp (word 204))) s = word att /\\
      read (memory :> bytes64(word(pc + got_stack_chk_guard))) s = guard /\\
      read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
      read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
      read (memory :> bytes(ea,el)) s = ev /\\
      (r = 13
       ==> !t. t < 2420
               ==> read (memory :> bytes8 (word_add sig (word t))) s =
                   (" ^ string_of_term SI44_SIGATT ^ ") t)");;

let SI44_ATT_PC_TAC =
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read PC s = x`) (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NUM_LT_CONV THENC REWRITE_CONV[]) th else th) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `read PC s = x`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC;;

(*** The end of a path at join11: the frame and the events (the callees'  ***)
(*** memory safety split with the definitions of their event variables)   ***)

let SI44_PATH_END_TAC =
  SIGN_BETA_ALL_TAC THEN SIGN_SELECT_TAC THEN SIGN_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [SIGN_PATH_UNIFY_TAC; SI44_LOOP_MEMACCESS_TAC];;

let SI44_ATT_FIN_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN (SI44_MAYCHANGE_TAC ORELSE SI44_PATH_END_TAC);;

let SI44_ATT_TEMPLATE =
 `\(sig:int64) (sk:int64) (fp:int64) (rho:num) (att:num) (C:num) (r:num) (x:num->int32)
   (b:num->byte) (guard:int64) (mf:int64) (mc:int64) (pc:num).
   APPEND (f_ev_cl sig sk fp rho att C r x b guard mf mc pc)
    (APPEND
      (if r < 4 then f_ev_pz sig sk fp rho att C r x b guard mf mc pc
       else if r < 12
       then if EVEN (r - 4) then f_ev_pw1 sig sk fp rho att C r x b guard mf mc pc
            else f_ev_pw2 sig sk fp rho att C r x b guard mf mc pc
       else f_ev_pt sig sk fp rho att C r x b guard mf mc pc)
      (f_ev_hd sig sk fp rho att C r x b guard mf mc pc))
   :(uarch_event)list`;;

let SI44_ATT_SETUP_TAC =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,_ = CONJ_PAIR th in
    MAP_EVERY (fun (th,n) -> SI_ASSUME_CALLEE_TAILED_TAC th n)
     [MP (SPEC_ALL SI44_HEAD) th,"H_HEAD"; MP (SPEC_ALL SI44_ZPRE) th,"H_ZPRE";
      MP (SPEC_ALL SI44_ZIT) th,"H_ZIT"; SI44_RPRE,"H_RPRE"; SI44_RIT,"H_RIT";
      SI44_TAIL,"H_TAIL"; MP (SPEC_ALL SI44_CLEAN) ms,"H_CLEAN"]) THEN
  CONCRETIZE_F_EVENTS_TAC SI44_ATT_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `sk:int64`; `skb:num->byte`; `fp:int64`;
    `rho:num`; `MU:num`; `RHO:num`; `att:num`; `C:num`; `r:num`; `x:num->int32`;
    `b:num->byte`; `guard:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst SI44_ATT_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SI44_ALIGNED16_32) THEN
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

(*** The challenge in the NTT domain at fp + 3168 in terms of C ***)

let SI44_ATT_CPH_TAC =
  FIRST_ASSUM(fun cth ->
    if can (term_match [] `num_of_bytelist l = (C:num)`) (concl cth) &&
       rhs(concl cth) = `C:num` then
      RULE_ASSUM_TAC(fun th ->
        let c = concl th in
        if can (find_term (fun t -> is_const t && fst(dest_const t) = "ensures")) c then th
        else if can (find_term (fun t -> is_const t && fst(dest_const t) = "mld_sign_cphat")) c
        then REWRITE_RULE[cth] (REWRITE_RULE[mld_sign_cphat] th) else th)
    else NO_TAC);;

(*** z_r fails, r < 4 ***)

let SI44_ATT_ZCASE_TAC =
  SUBGOAL_THEN `r <= 4 /\ ~(r = 13)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `r < 4` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `r < 4 ==> P`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SI44_ATT_CALL_TAC "H_ZPRE"
   [`r:num`; `sig:int64`; `sk:int64`; `skb:num->byte`; `fp:int64`; SI44_ATT_CPH;
    `RHO:num`; `att:num`; `pc:num`] 2 THEN
  SI44_ATT_PC_TAC THEN
  SI44_ATT_CALL_TAC "H_ZIT"
   [`F`; `sig:int64`; `sk:int64`; `skb:num->byte`; `fp:int64`; `r:num`; SI44_ATT_CPH;
    `RHO:num`; `att:num`; `pc:num`] 3 THEN
  SI44_ATT_PC_TAC THEN
  ARM_STEPS_TAC SI44_ATT_EXEC (4--8) THEN
  SI44_ATT_FIN_TAC;;

(*** check r - 4 of the rows fails, 4 <= r < 12 ***)

let SI44_ATT_ROWSLICE_TAC m st =
  MP_TAC(SPECL [`fp:int64`; `4192`; `1024`; `mld_poly_decompose_lo_88`; SI44_ATT_W; m; st]
               SIGN_ROW_SLICE) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [m; st]
             `!k. 256 * m <= k /\ k < 1024
                  ==> read (memory :> bytes32 (word_add fp (word (4192 + 4 * k)))) st = Q k`)
           (concl th)
    then REWRITE_TAC[th] else NO_TAC) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC];;

let SI44_ATT_WCASE_TAC =
  SUBGOAL_THEN `(r - 4) DIV 2 <= 4 /\ (r - 4) DIV 2 < 4 /\ ~(r = 13) /\
                2 * (r - 4) DIV 2 <= r - 4`
   STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `r < 12` THEN UNDISCH_TAC `4 <= r` THEN
    SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [SI44_ATT_R0; SI44_ATT_CT0; `95154`; `95232`; `r - 4`;
                `(r - 4) DIV 2`] SIGN_ROWS_GOOD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `j:num` o REWRITE_RULE[ASSUME `4 <= r`] o
      check (fun th -> can (term_match []
        `4 <= r ==> (!j. j < r - 4 /\ j < 8 ==> P j)`) (concl th))) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `j < r - 4` THEN UNDISCH_TAC `r < 12` THEN ARITH_TAC;
    DISCH_TAC] THEN
  SI44_ATT_CALL_TAC "H_ZPRE"
   [`4`; `sig:int64`; `sk:int64`; `skb:num->byte`; `fp:int64`; SI44_ATT_CPH;
    `RHO:num`; `att:num`; `pc:num`] 2 THEN
  SI44_ATT_PC_TAC THEN
  SI44_ATT_CALL_TAC "H_RPRE"
   [`(r - 4) DIV 2`; `sk:int64`; `skb:num->byte`; `fp:int64`; SI44_ATT_W; SI44_ATT_CPH;
    `pc:num`] 3 THEN
  SI44_ATT_PC_TAC THEN
  SI44_ATT_ROWSLICE_TAC `(r - 4) DIV 2` `s3:armstate` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `4 <= r /\ r < 12 ==> ~(P = word 0:int32)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `EVEN(r - 4)` THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `~(mld_poly_chknorm (if EVEN(r - 4) then a else b) (word w) = word 0)`)
      (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SI44_ATT_CALL_TAC "H_RIT"
     [`F`; `F`; `sk:int64`; `skb:num->byte`; `fp:int64`; `(r - 4) DIV 2`; SI44_ATT_W;
      SI44_ATT_CPH; `pc:num`] 4;
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `~(mld_poly_chknorm (if EVEN(r - 4) then a else b) (word w) = word 0)`)
      (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
     (SPECL [`4`; `r:num`] SIGN_ODD_ROW)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `r - 5` o REWRITE_RULE[ASSUME `4 <= r`] o
      check (fun th -> can (term_match []
        `4 <= r ==> (!j. j < r - 4 /\ j < 8 ==> P j)`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [UNDISCH_TAC `r < 12` THEN ARITH_TAC; DISCH_TAC] THEN
    SI44_ATT_CALL_TAC "H_RIT"
     [`T`; `F`; `sk:int64`; `skb:num->byte`; `fp:int64`; `(r - 4) DIV 2`; SI44_ATT_W;
      SI44_ATT_CPH; `pc:num`] 4] THEN
  SI44_ATT_PC_TAC THEN
  ARM_STEPS_TAC SI44_ATT_EXEC (5--9) THEN
  SI44_ATT_FIN_TAC;;

(*** the hints, r = 12 (too many) or 13 (success), both through TAIL ***)

let SI44_ATT_FACT_RW_TAC th =
  RULE_ASSUM_TAC(fun th' ->
    if can (find_term (fun t -> is_const t && fst(dest_const t) = "ensures")) (concl th') ||
       concl th' = concl th
    then th' else REWRITE_RULE[th] th');;

let SI44_ATT_TCASE_TAC =
  SUBGOAL_THEN `12 <= r /\ 4 <= 4` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(r < 12)` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [SI44_ATT_R0; SI44_ATT_CT0; `95154`; `95232`; `8`; `4`] SIGN_ROWS_GOOD) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[LE_REFL] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `j:num` o REWRITE_RULE[ASSUME `4 <= r`] o
      check (fun th -> can (term_match []
        `4 <= r ==> (!j. j < r - 4 /\ j < 8 ==> P j)`) (concl th))) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `12 <= r` THEN UNDISCH_TAC `j < 8` THEN ARITH_TAC;
    DISCH_TAC] THEN
  SI44_ATT_CALL_TAC "H_ZPRE"
   [`4`; `sig:int64`; `sk:int64`; `skb:num->byte`; `fp:int64`; SI44_ATT_CPH;
    `RHO:num`; `att:num`; `pc:num`] 2 THEN
  SI44_ATT_PC_TAC THEN
  SI44_ATT_CALL_TAC "H_RPRE"
   [`4`; `sk:int64`; `skb:num->byte`; `fp:int64`; SI44_ATT_W; SI44_ATT_CPH; `pc:num`] 3 THEN
  SI44_ATT_PC_TAC THEN
  SI44_ASM_RW_TAC[ARITH_RULE `256 * 4 = 1024`] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `(if 12 <= r then p else q) = (x:num->int32)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
    SI44_ATT_FACT_RW_TAC th THEN ASSUME_TAC th) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `(if 12 <= r then p else q) = (b:num->byte)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!j. j < 768
        ==> read (memory :> bytes8 (word_add fp (word (8288 + j)))) s3 =
            (b:num->byte) j`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(fun th ->
      if is_var(rhs(concl th)) && name_of(rhs(concl th)) = "b"
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[mld_sign_hint_w1] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SI44_ATT_CALL_TAC "H_TAIL"
   [`sig:int64`; `fp:int64`; `C:num`; `x:num->int32`; `b:num->byte`; `pc:num`] 4 THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `12 <= r ==> (r = 13 <=> P)`) (concl th))) THEN
  ASM_REWRITE_TAC[NOT_LT] THEN DISCH_TAC THEN
  ASM_CASES_TAC `r = 13` THENL
   [SUBGOAL_THEN `mld_hint_count (mld_polyvec_make_hint_88 x b) 1024 <= 80` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if is_iff(concl th) && lhs(concl th) = `r = 13`
                            then ACCEPT_TAC(EQ_MP th (ASSUME `r = 13`)) else NO_TAC); ALL_TAC] THEN
    SI44_ATT_FACT_RW_TAC
      (ASSUME `mld_hint_count (mld_polyvec_make_hint_88 x b) 1024 <= 80`) THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [`sig:int64`; `C:num`] `read (memory :> bytes (sig,32)) s = C`)
             (concl th)
      then FIRST_ASSUM(fun cth ->
             if is_var(rhs(concl cth)) && name_of(rhs(concl cth)) = "C" &&
                can (term_match [] `num_of_bytelist l = (C:num)`) (concl cth)
             then ASSUME_TAC(MATCH_MP SIGN_BYTES8_OF_READ_BYTES (TRANS th (SYM cth)))
             else NO_TAC)
      else NO_TAC) THEN
    REPEAT(FIRST_X_ASSUM(fun th -> if concl th = `r = 13` then ASSUME_TAC(EQT_INTRO th)
                                   else NO_TAC)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(REWRITE_TAC[mld_sign_attempt_sig] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[mld_sign_cphat] THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `2420 = (32 + 4 * 576) + 84` SUBST1_TAC THENL
       [ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC SIGN_SIG_ASSEMBLE THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(ACCEPT_TAC o CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
        check (fun th -> can (term_match []
          `!t. t < 576 * 4
               ==> read (memory :> bytes8 (word_add sig (word (32 + t)))) s =
                   P t`) (concl th))) THEN NO_TAC) THEN
    (SI44_MAYCHANGE_TAC ORELSE SI44_PATH_END_TAC);
    SUBGOAL_THEN `~(mld_hint_count (mld_polyvec_make_hint_88 x b) 1024 <= 80)` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if is_iff(concl th) && lhs(concl th) = `r = 13`
                            then MP_TAC th else NO_TAC) THEN
      REWRITE_TAC[ASSUME `~(r = 13)`]; ALL_TAC] THEN
    SI44_ATT_FACT_RW_TAC
      (ASSUME `~(mld_hint_count (mld_polyvec_make_hint_88 x b) 1024 <= 80)`) THEN
    SI44_ATT_FIN_TAC];;

let SI44_ATT_PATHS_TAC =
  ASM_CASES_TAC `r < 4` THENL
   [SI44_ATT_ZCASE_TAC;
    SUBGOAL_THEN `4 <= r /\ 4 <= 4` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~(r < 4)` THEN ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `4 <= r ==> (!i. i < 4 ==> P i)`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_CASES_TAC `r < 12` THENL [SI44_ATT_WCASE_TAC; SI44_ATT_TCASE_TAC]];;

let SI44_ATT_CLEAN_TAC =
  FULL_INIT_TAC THEN
  SI44_ATT_CALL_TAC "H_CLEAN" [`r = 13`; `att:num`; `fp:int64`; `pc:num`] 1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  (SI44_MAYCHANGE_TAC ORELSE
   (SAFE_META_EXISTS_TAC allowed_vars_e THEN
    CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
    CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; SI44_LOOP_MEMACCESS_TAC]));;

let SI44_ATT = prove
 (SI44_ATT_STMT,
  SI44_ATT_SETUP_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa44_signature_internal_join11` SI44_ATT_MID THEN
  CONJ_TAC THENL
   [FULL_INIT_TAC THEN
    SI44_ATT_CALL_TAC "H_HEAD"
     [`fp:int64`; `att:num`; `rho:num`; `RHO:num`; `MU:num`; `C:num`; `guard:int64`;
      `pc:num`] 1 THEN
    SI44_ATT_CPH_TAC THEN SI44_ATT_PATHS_TAC;
    SI44_ATT_CLEAN_TAC]);;
