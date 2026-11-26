(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The stages of an attempt of mldsa87_signature_internal (clang 23 -O3 mono *)
(* reduced-RAM), as FULL lemmas for segments of the code, templated from     *)
(* those of mldsa44_signature_internal (signature_internal_44_stages.ml) and *)
(* of the x86 proof of the same function, with the region lemmas of         *)
(* signature_internal_87_inline.ml for the inlined code. fp is the stack     *)
(* pointer after the prologue (aligned to 32); the callees use at most 1472  *)
(* bytes below it, so the frame of the stages is fp - 1472 .. fp + 15456.    *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/signature_internal_87_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/signature_internal_87_inline.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_ntt_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/utils/mldsa_native_signing.ml";;
needs "arm/proofs/utils/mldsa_native_lazy_matrix.ml";;
needs "arm/proofs/utils/mldsa_native_wrap.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_challenge_87_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_uniform_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/lazy_eq_spec.ml";;

let SI87_EXEC_RANGE lo hi =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   ([(layout ("mldsa87_signature_internal_" ^ lo),
      layout ("mldsa87_signature_internal_" ^ hi))] @
    [layout_range "plt_memcpy"; layout_range "plt_memset"]);;

(*** fp as fb_si + d in the goal and the assumptions, so that the memory    ***)
(*** safety checks compare regions with one base and no offsets that wrap  ***)
(*** (as SI_FB_NORM_TAC of x86's inline_sign_stage.ml, with fp for rsp0)       ***)

let SI87_FB_NORM_TAC d =
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

let SI87_SAFETY_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  (CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]) THEN
  SI87_FB_NORM_TAC 1472 THEN
  REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN
  REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

(*** ASSUME_CALLEE_SAFETY_TAILED_TAC for a stage lemma with many variables: ***)
(*** the same assumption, with the quantifiers rotated by a derived rule   ***)
(*** rather than by MESON, which gives up ("Too deep") beyond about ten    ***)
(*** variables (as SI_ASSUME_CALLEE_TAILED_TAC of x86's inline_sign_stage.ml). ***)

let SI87_ASSUME_CALLEE_TAILED_TAC =
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

let SI87_GOT_TAC =
  W(fun (asl,w) ->
    MAP_EVERY (fun (_,th) ->
      let c = concl th in
      if is_eq c &&
         can (term_match [] `read (memory :> bytes64 (word (pc + n))) s`) (lhs c)
      then ASSUME_TAC(REWRITE_RULE[WORD_ADD] th) else ALL_TAC) asl);;

(*** A call of memset through the PLT, the BL being step n ***)

let SI87_MEMSET_TAC exec allowed n =
  LIBC_PLT_TAC exec n THEN
  G1_LIBC_CALL_TAC "H_MEMSET" exec
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`]
   allowed (n + 5);;

(* ------------------------------------------------------------------------- *)
(* The cleanup of an attempt (CLEAN), from join12 with w19 = 1 on success    *)
(* and 0 otherwise: the memsets of z (fp + 2048), c (fp + 3072), w (fp +     *)
(* 4096), w1 packed (fp + 12288) and the scratch polynomial (fp + 13312),    *)
(* the zeroing of the structure of rho'' (fp + 14336) and of c~ (fp +        *)
(* 14368), and the test of w19: to loop2_exit2 on success, else to the next  *)
(* attempt (loop2, with the count att + 1 in w9) or, after the last, to      *)
(* loop2_exit1. The count is tested as att / 16 <= 584 (lsr #4, b.ls).       *)
(* ------------------------------------------------------------------------- *)

let SI87_CLEAN_STMT =
 `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e ok att fp pc.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 fp /\ att < 9361 /\
          ALL (nonoverlapping (word_sub fp (word 1472),16928))
              [(word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa87_signature_internal_join12) /\
                    read SP s = fp /\
                    read X19 s = (if ok then word 1 else word 0) /\
                    read (memory :> bytes32 (word_add fp (word 100))) s = word att /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read events s = e)
               (\s. read PC s =
                    (if ok then word (pc + mldsa87_signature_internal_loop2_exit2)
                     else if att + 1 < 9361
                     then word (pc + mldsa87_signature_internal_loop2)
                     else word (pc + mldsa87_signature_internal_loop2_exit1)) /\
                    read SP s = fp /\ read Q7 s = word 0 /\
                    (~ok ==> read X9 s = word (att + 1)) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (exists e2. read events s = APPEND e2 e /\
                       e2 = f_events ok att fp mf pc /\
                       memaccess_inbounds e2
                        [word_sub fp (word 1472),16928; word(pc + got_memset),8; ea,el]
                        [word_sub fp (word 1472),16928]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
                MAYCHANGE [memory :> bytes(word_add fp (word 2048),1024);
                           memory :> bytes(word_add fp (word 3072),1024);
                           memory :> bytes(word_add fp (word 4096),8192);
                           memory :> bytes(word_add fp (word 12288),1024);
                           memory :> bytes(word_add fp (word 13312),1024);
                           memory :> bytes(word_add fp (word 14336),16);
                           memory :> bytes(word_add fp (word 14368),64)])`;;

let SI87_CLEAN_EXEC = SI87_EXEC_RANGE "join12" "loop2_exit1";;

(*** The test of the count of the attempts (lsr w8, w9, #4; cmp w8, #584; ***)
(*** b.ls) and the next count                                              ***)

let SI87_ATT_TEST = prove
 (`!att. att < 9361
         ==> (~(&(val (word_ushr (word att:int32) 4)) - &584:int =
                &(val (word_sub (word_ushr (word att:int32) 4) (word 584))) /\
              ~(val (word_sub (word_ushr (word att:int32) 4) (word 584)) = 0)) <=>
              att + 1 < 9361)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`word_ushr (word att:int32) 4`; `584`] GLUE_FLAGS_LS) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VAL_WORD_USHR; VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `att MOD 4294967296 = att` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `x <= 584 <=> x < 585`] THEN
  SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC);;

let SI87_ATT_INC = prove
 (`!att. att < 9361
         ==> word_zx (word_add (word att:int32) (word 1)):int64 = word (att + 1)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD; DIMINDEX_32;
              DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `att MOD 4294967296 = att /\ (att + 1) MOD 4294967296 = att + 1 /\
                (att + 1) MOD 18446744073709551616 = att + 1` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_REWRITE_TAC[]]);;

(*** Split on a boolean p, rewriting the other assumptions with it ***)

let SI87_CASES_TAC p =
  ASM_CASES_TAC p THEN
  FIRST_ASSUM(fun th -> if concl th = p || concl th = mk_neg p
    then RULE_ASSUM_TAC(fun th' -> if concl th' = concl th then th'
                                   else REWRITE_RULE[th] th')
    else NO_TAC);;

let SI87_CLEAN = prove
 (SI87_CLEAN_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[memset_full_contract] th) "H_MEMSET") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(ok:bool) (att:num) (fp:int64) (mf:int64) (pc:num).
      if ok then f_ev_ok fp mf pc
      else if att + 1 < 9361 then f_ev_nx fp mf pc
      else f_ev_ex fp mf pc:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `ok:bool`; `att:num`; `fp:int64`;
                       `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; fst SI87_CLEAN_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN SI87_GOT_TAC THEN
  (let ms = SI87_MEMSET_TAC SI87_CLEAN_EXEC [`fp:int64`; `mf:int64`; `pc:num`] in
   ARM_STEPS_TAC SI87_CLEAN_EXEC (1--4) THEN ms 4 THEN
   ARM_STEPS_TAC SI87_CLEAN_EXEC (10--13) THEN ms 13 THEN
   ARM_STEPS_TAC SI87_CLEAN_EXEC (19--23) THEN ms 23 THEN
   ARM_STEPS_TAC SI87_CLEAN_EXEC (29--33) THEN ms 33 THEN
   ARM_STEPS_TAC SI87_CLEAN_EXEC (39--44) THEN ms 44 THEN
   ARM_STEPS_TAC SI87_CLEAN_EXEC (50--61)) THEN
  SI87_CASES_TAC `ok:bool` THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV WORD_RED_CONV)) THEN ASM_REWRITE_TAC[] THENL
   [ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SI87_SAFETY_TAC;
    ALL_TAC] THEN
  ARM_STEPS_TAC SI87_CLEAN_EXEC (62--66) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `att:num` SI87_ATT_TEST) (ASSUME `att < 9361`);
    MP (SPEC `att:num` SI87_ATT_INC) (ASSUME `att < 9361`)]) THEN
  SI87_CASES_TAC `att + 1 < 9361` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SI87_SAFETY_TAC);;

(* ------------------------------------------------------------------------- *)
(* s2 and t0 in the NTT domain, as in the 44 stages (offsets of ML-DSA-87:   *)
(* s2 at sk + 800, t0 at sk + 1568).                                        *)
(* ------------------------------------------------------------------------- *)

let SI87_S2U =
 `mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte)(800 + j))`;;
let SI87_S2H = mk_comb(`mld_polyvec_map mld_poly_ntt`,SI87_S2U);;
let SI87_T0U =
 `mld_polyvec_unpack 416 mld_polyt0_unpack (\j. (skb:num->byte)(1568 + j))`;;
let SI87_T0H = mk_comb(`mld_polyvec_map mld_poly_ntt`,SI87_T0U);;

(* ------------------------------------------------------------------------- *)
(* One iteration of the loop over the rows of w0 (RIT), from loop52 with row *)
(* j in x23 (96 j in x19, the row at fp + 4096 + 1024 j in x24): s2_j        *)
(* unpacked into the scratch polynomial at fp + 13312 and transformed, its   *)
(* product with the challenge, w0_j - c s2_j in place and reduced, its norm  *)
(* check; then t0_j likewise, c t0_j reduced and checked, and the sum in     *)
(* place in row j. ok1 and ok2 are the results of the two checks (ok2        *)
(* matters only when ok1 holds): if both pass, the code goes back to loop52  *)
(* or, after the last row, to loop52_exit1, else to the rejection at join11. *)
(* ------------------------------------------------------------------------- *)

let SI87_RIT_R0 = list_mk_comb(`mld_sign_r0`,
  [`mld_poly_decompose_lo_32`; `w:num->int32`; SI87_S2H; `cphat:num->int32`; `j:num`]);;
let SI87_RIT_CT0 = list_mk_comb(`mld_sign_ct0`, [SI87_T0H; `cphat:num->int32`; `j:num`]);;

let SI87_PC245760 = SI87_PAGES SI87_PAGE_REGS;;

let SI87_RIT_PRE =
 "read SP s = fp /\\
  read X27 s = word_add fp (word 13312) /\\ read X0 s = word 2 /\\
  read X28 s = word 18446744073701171199 /\\ read X26 s = word 252236767799803904 /\\
  read (memory :> bytes64 (word_add fp (word 104))) s = word_add fp (word 3080) /\\
  read (memory :> bytes64 (word_add fp (word 640))) s = word_add sk (word 800) /\\
  read (memory :> bytes64 (word_add fp (word 672))) s = word_add sk (word 1568) /\\
  read (memory :> bytes128 (word_add fp (word 192))) s =
  word 339618401959998730991157055895298383871 /\\
  (!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (3072 + 4 * i)))) s =
                   cphat i) /\\
  (!i. i < 4896 ==> read (memory :> bytes8 (word_add sk (word i))) s = skb i)";;

let SI87_RIT_STMT = parse_term(
 "exists f_events.
    forall e ok1 ok2 sk skb fp j w cphat pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 16 fp /\\ j < 8 /\\
      (ok1 <=> mld_poly_chknorm (" ^ string_of_term SI87_RIT_R0 ^ ") (word 261768) = word 0) /\\
      (ok1 ==> (ok2 <=> mld_poly_chknorm (" ^ string_of_term SI87_RIT_CT0 ^ ") (word 261888) =
                        word 0)) /\\
      ALL (nonoverlapping (word_sub fp (word 1472),16928))
          [(sk,4896); (word pc,libmldsa_size)]
      ==> ensures arm
           (\\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read PC s = word (pc + mldsa87_signature_internal_loop52) /\\
                read X23 s = word j /\\ read X19 s = word (96 * j) /\\
                read X24 s = word_add fp (word (4096 + 1024 * j)) /\\ " ^ SI87_PC245760 ^
 "              read (memory :> bytes64 (word_add fp (word 168))) s = word (6 + 416 * j) /\\
                read (memory :> bytes64 (word_add fp (word 208))) s =
                word_add fp (word (4112 + 1024 * j)) /\\\n" ^ SI87_RIT_PRE ^ " /\\
                (!i. i < 256 ==> read (memory :> bytes32
                                   (word_add fp (word ((4096 + 1024 * j) + 4 * i)))) s =
                                 mld_poly_decompose_lo_32 (mld_poly_of w j) i) /\\
                read events s = e)
           (\\s. read PC s =
                (if ok1 /\\ ok2
                 then (if j + 1 < 8 then word (pc + mldsa87_signature_internal_loop52)
                       else word (pc + mldsa87_signature_internal_loop52_exit1))
                 else word (pc + mldsa87_signature_internal_join11)) /\\
                read SP s = fp /\\
                (ok1 /\\ ok2
                 ==> read X23 s = word (j + 1) /\\ read X19 s = word (96 * (j + 1)) /\\
                     read X24 s = word_add fp (word (4096 + 1024 * (j + 1))) /\\
                     read X0 s = word 2 /\\ read X14 s = word 523777 /\\ " ^ SI87_PC245760 ^
 "                   read (memory :> bytes64 (word_add fp (word 168))) s =
                     word (6 + 416 * (j + 1)) /\\
                     read (memory :> bytes64 (word_add fp (word 208))) s =
                     word_add fp (word (4112 + 1024 * (j + 1))) /\\
                     (!i. i < 256 ==> read (memory :> bytes32
                                        (word_add fp (word ((4096 + 1024 * j) + 4 * i)))) s =
                                      mld_poly_add (" ^ string_of_term SI87_RIT_R0 ^ ")
                                                   (" ^ string_of_term SI87_RIT_CT0 ^ ") i)) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events ok1 ok2 sk fp j pc /\\
                   memaccess_inbounds e2
                    [sk,4896; word_sub fp (word 1472),16928;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa87_signature_internal_consts),400]
                    [word_sub fp (word 1472),16928]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [X18; X19; X20; X23; X24; X30] ,,
            MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
            MAYCHANGE [memory :> bytes(word_sub fp (word 208),208);
                       memory :> bytes(word_add fp (word 168),8);
                       memory :> bytes(word_add fp (word 208),8);
                       memory :> bytes(word_add fp (word 224),416);
                       memory :> bytes(word_add fp (word (4096 + 1024 * j)),1024);
                       memory :> bytes(word_add fp (word 13312),1024)])");;

let SI87_RIT_EXEC = SI87_EXEC_RANGE "loop52" "loop52_exit1";;

let SI87_RIT_TEMPLATE =
 `\(ok1:bool) (ok2:bool) (sk:int64) (fp:int64) (j:num) (pc:num).
   if ok1 then
    (if ok2 then (if j + 1 < 8 then f_ev_mid sk fp j pc else f_ev_last sk fp j pc)
     else f_ev_f2 sk fp j pc)
   else f_ev_f1 sk fp j pc :(uarch_event)list`;;

let SI87_RIT_ALLOWED = [`ok1:bool`; `ok2:bool`; `sk:int64`; `fp:int64`; `j:num`; `pc:num`];;

let SI87_RIT_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc SI87_RIT_EXEC
    name ilist SI87_RIT_ALLOWED n;;

(*** Bytes off .. off + n - 1 of the secret key at state st ***)

let SI87_SK_SLICE_TAC off n st =
  let t = vsubst [st,`s:armstate`] (parse_term(Printf.sprintf
   "!k. k < %d ==> read (memory :> bytes8 (word_add sk (word (%s + k)))) s =
                   (skb:num->byte) (%s + k)" n off off)) in
  SUBGOAL_THEN t ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (term_match []
       `!i. i < 4896 ==> read (memory :> bytes8 (word_add sk (word i))) s = skb i`)
       (concl th))) THEN
    MAP_EVERY UNDISCH_TAC [`j < 8`; mk_binop `(<):num->num->bool` `k:num` (mk_small_numeral n)] THEN
    ARITH_TAC;
    ALL_TAC];;

let SI87_SK_SLICE2_TAC aoff voff n st =
  let t = vsubst [st,`s:armstate`] (parse_term(Printf.sprintf
   "!k. k < %d ==> read (memory :> bytes8 (word_add sk (word (%s + k)))) s =
                   (skb:num->byte) (%s + k)" n aoff voff)) in
  SUBGOAL_THEN t ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (term_match []
       `!i. i < 4896 ==> read (memory :> bytes8 (word_add sk (word i))) s = skb i`)
       (concl th))) THEN
    MAP_EVERY UNDISCH_TAC [`j < 8`; mk_binop `(<):num->num->bool` `k:num` (mk_small_numeral n)] THEN
    ARITH_TAC;
    ALL_TAC];;

(*** A register fact restated in the form a precondition needs (state n) ***)

let SI87_REG_FORM_TAC reg n (nw:term) =
  let s = mk_var("s"^string_of_int n,`:armstate`) in
  let lh = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                           mk_const(reg,[])),s) in
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = lh
    then let tm = mk_eq(rhs(concl th),nw) in
         let eth = try prove(tm, CONV_TAC(DEPTH_CONV WORD_RED_CONV))
                   with Failure _ -> WORD_RULE tm in
         ASSUME_TAC(TRANS th eth) else NO_TAC);;

let SI87_ORIENT_TAC =
  FIRST_X_ASSUM(fun th -> if is_iff(concl th) && lhs(concl th) = `ok1:bool`
                          then ASSUME_TAC(GSYM th) else NO_TAC) THEN
  FIRST_X_ASSUM(fun th -> if is_imp(concl th) && lhand(concl th) = `ok1:bool`
                          then ASSUME_TAC(CONV_RULE(RAND_CONV SYM_CONV) th) else NO_TAC);;

let SI87_DECIDE_TAC okv =
  FIRST_X_ASSUM(fun th ->
    if is_iff(concl th) && rhs(concl th) = okv then
      RULE_ASSUM_TAC(fun th' ->
        if can (term_match [] `read PC s = x`) (concl th') ||
           can (term_match [] `read events s = x`) (concl th')
        then REWRITE_RULE[th] (REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0] th')
        else th')
    else NO_TAC);;

(*** The end of a stage: the frame (callees below fp) and the events ***)

let SI87_MAYCHANGE_TAC =
  W(fun (asl,w) -> if maychange_term w then ALL_TAC else NO_TAC) THEN
  SI87_FB_NORM_TAC 1472 THEN
  FIRST_X_ASSUM(fun th -> if maychange_term (concl th) && not(is_forall(concl th))
                          then MP_TAC th else NO_TAC) THEN
  DISCH_TAC THEN MONOTONE_MAYCHANGE_TAC;;

let SI87_END_TAC = REPEAT CONJ_TAC THEN (SI87_MAYCHANGE_TAC ORELSE SI87_SAFETY_TAC);;

let SI87_RIT_FAIL_TAC okv =
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read PC s = x`) (concl th)
                           then REWRITE_RULE[ASSUME(mk_neg okv)] th else th) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SI87_END_TAC;;

let SI87_RIT_POLY v = mk_comb(mk_comb(`mld_poly_of`,v),`j:num`);;
let SI87_RIT_PW1 = list_mk_comb(`mld_poly_pointwise_montgomery`,
  [SI87_RIT_POLY SI87_S2H; `cphat:num->int32`]);;
let SI87_RIT_PW2 = list_mk_comb(`mld_poly_pointwise_montgomery`,
  [SI87_RIT_POLY SI87_T0H; `cphat:num->int32`]);;
let SI87_RIT_CS2 = mk_comb(`mld_poly_invntt_tomont`,SI87_RIT_PW1);;
let SI87_RIT_W0J = `mld_poly_decompose_lo_32 (mld_poly_of (w:num->int32) j)`;;
let SI87_RIT_SUBX = list_mk_comb(`mld_poly_sub`,[SI87_RIT_W0J; SI87_RIT_CS2]);;

let SI87_LK l name =
  try assoc name l with Failure _ -> assoc ("mldsa87_signature_internal_" ^ name) l;;

let SI87_RIT_CALLEES () =
  [SI87_ETA_RTH,"H_ETA"; SI87_LK SI87_T0UNP "loop58","H_T0U";
   MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_NTT";
   MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_INV";
   SI87_LK SI87_PWM "loop55","H_PWM55"; SI87_LK SI87_PWM "loop59","H_PWM59";
   SI87_RSUB,"H_RSUB"; SI87_LK SI87_RED "loop56","H_RED56";
   SI87_LK SI87_CHK "loop57","H_CHK57"; SI87_LK SI87_RED "loop60","H_RED60";
   SI87_LK SI87_CHK "loop61","H_CHK61"; SI87_RADD,"H_RADD"];;

(*** From loop52 to the first check (step 21) ***)

let SI87_RIT_PART1_TAC =
  SI87_SK_SLICE_TAC "800 + 96 * j" 96 `s0:armstate` THEN
  SI87_RIT_CALL_TAC "H_ETA" [`fp:int64`; `word_add sk (word 800):int64`; `j:num`;
    `\k. (skb:num->byte) (800 + 96 * j + k)`; `pc:num`] 1 THEN
  MLD_LAZY_REPOLY_TAC `mld_polyeta_unpack_2 (\k. (skb:num->byte) (800 + 96 * j + k))`
    (SI87_RIT_POLY SI87_S2U) [mld_polyvec_unpack; MLD_POLY_OF_POLYVEC] THEN
  ARM_STEPS_TAC SI87_RIT_EXEC (2--4) THEN
  SI87_RIT_CALL_TAC "H_NTT" [`read X0 s`; SI87_RIT_POLY SI87_S2U; `pc:num`;
                              `read SP s`; `read X30 s`] 5 THEN
  MLD_LAZY_REPOLY_TAC (mk_comb(`mld_poly_ntt`,SI87_RIT_POLY SI87_S2U))
    (SI87_RIT_POLY SI87_S2H) [MLD_POLY_OF_POLYVEC_MAP] THEN
  ARM_STEPS_TAC SI87_RIT_EXEC (6--8) THEN
  SI87_RIT_CALL_TAC "H_PWM55" [`word_add fp (word 13312):int64`;
    `word_add fp (word 3072):int64`; SI87_RIT_POLY SI87_S2H; `cphat:num->int32`;
    `pc:num`] 9 THEN
  ARM_STEPS_TAC SI87_RIT_EXEC (10--12) THEN
  SI87_RIT_CALL_TAC "H_INV" [`read X0 s`; SI87_RIT_PW1; `pc:num`; `read SP s`;
                              `read X30 s`] 13 THEN
  SI87_RIT_CALL_TAC "H_RSUB" [`fp:int64`; `word_add fp (word (4096 + 1024 * j)):int64`;
    SI87_RIT_W0J; SI87_RIT_CS2; `j:num`; `word_add fp (word (4112 + 1024 * j)):int64`;
    `pc:num`] 14 THEN
  SI87_REG_FORM_TAC "X8" 14 `word_add fp (word ((4096 + 1024 * j) + 16)):int64` THEN
  SI87_RIT_CALL_TAC "H_RED56" [`word_add fp (word (4096 + 1024 * j)):int64`;
    SI87_RIT_SUBX; `pc:num`] 15 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_r0]) THEN
  ARM_STEPS_TAC SI87_RIT_EXEC (16--19) THEN
  SI87_REG_FORM_TAC "X13" 19 `word_zx (word_sub (word 261768:int32) (word 1)):int64` THEN
  SI87_REG_FORM_TAC "X8" 19 `word_zx (word 0:int32):int64` THEN
  SI87_RIT_CALL_TAC "H_CHK57" [`word_add fp (word (4096 + 1024 * j)):int64`;
    SI87_RIT_R0; `word 261768:int32`; `word 0:int32`; `pc:num`] 20 THEN
  ARM_STEPS_TAC SI87_RIT_EXEC [21] THEN
  SI87_DECIDE_TAC `ok1:bool` THEN SI87_CASES_TAC `ok1:bool` THENL
   [ALL_TAC; SI87_RIT_FAIL_TAC `ok1:bool`];;

(*** From the first check to the second (step 51) ***)

let SI87_RIT_PART2_TAC =
  ARM_STEPS_TAC SI87_RIT_EXEC (22--25) THEN
  SI87_REG_FORM_TAC "X9" 25 `word_add sk (word ((1568 + 416 * j) + 6)):int64` THEN
  SI87_SK_SLICE2_TAC "(1568 + 416 * j)" "1568 + 416 * j" 416 `s25:armstate` THEN
  SI87_RIT_CALL_TAC "H_T0U" [`word_add fp (word 13312):int64`;
    `word_add sk (word (1568 + 416 * j)):int64`;
    `\k. (skb:num->byte) (1568 + 416 * j + k)`; `pc:num`] 26 THEN
  MLD_LAZY_REPOLY_TAC `mld_polyt0_unpack (\k. (skb:num->byte) (1568 + 416 * j + k))`
    (SI87_RIT_POLY SI87_T0U) [mld_polyvec_unpack; MLD_POLY_OF_POLYVEC] THEN
  ARM_STEPS_TAC SI87_RIT_EXEC (27--29) THEN
  SI87_RIT_CALL_TAC "H_NTT" [`read X0 s`; SI87_RIT_POLY SI87_T0U; `pc:num`;
                              `read SP s`; `read X30 s`] 30 THEN
  MLD_LAZY_REPOLY_TAC (mk_comb(`mld_poly_ntt`,SI87_RIT_POLY SI87_T0U))
    (SI87_RIT_POLY SI87_T0H) [MLD_POLY_OF_POLYVEC_MAP] THEN
  ARM_STEPS_TAC SI87_RIT_EXEC (31--33) THEN
  SI87_RIT_CALL_TAC "H_PWM59" [`word_add fp (word 13312):int64`;
    `word_add fp (word 3072):int64`; SI87_RIT_POLY SI87_T0H; `cphat:num->int32`;
    `pc:num`] 34 THEN
  ARM_STEPS_TAC SI87_RIT_EXEC (35--37) THEN
  SI87_RIT_CALL_TAC "H_INV" [`read X0 s`; SI87_RIT_PW2; `pc:num`; `read SP s`;
                              `read X30 s`] 38 THEN
  ARM_STEPS_TAC SI87_RIT_EXEC (39--41) THEN
  SI87_RIT_CALL_TAC "H_RED60" [`word_add fp (word 13312):int64`;
    mk_comb(`mld_poly_invntt_tomont`,SI87_RIT_PW2); `pc:num`] 42 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_ct0]) THEN
  ARM_STEPS_TAC SI87_RIT_EXEC (43--49) THEN
  SI87_REG_FORM_TAC "X13" 49
    `word_zx (word_sub (word_sub (word 261888:int32) (word 1)) (word 120)):int64` THEN
  SI87_REG_FORM_TAC "X8" 49 `word_zx (word 0:int32):int64` THEN
  SI87_REG_FORM_TAC "X14" 49 `word 523777:int64` THEN
  SI87_RIT_CALL_TAC "H_CHK61" [`word_add fp (word 13312):int64`;
    SI87_RIT_CT0; `word 261888:int32`; `word 0:int32`; `pc:num`] 50 THEN
  ARM_STEPS_TAC SI87_RIT_EXEC [51] THEN
  SI87_DECIDE_TAC `ok2:bool` THEN SI87_CASES_TAC `ok2:bool` THENL
   [ALL_TAC; SI87_RIT_FAIL_TAC `ok2:bool`];;

let SI87_RIT_LAST = prove
 (`!j. j < 8 ==> (j + 1 = 8 <=> ~(j + 1 < 8))`, ARITH_TAC);;

(*** The sum of the row and the back edge ***)

let SI87_RIT_PART3_TAC =
  SI87_RIT_CALL_TAC "H_RADD" [`fp:int64`; `word_add fp (word (4096 + 1024 * j)):int64`;
    SI87_RIT_R0; SI87_RIT_CT0; `j:num`; `96 * j`;
    `word_add fp (word (4096 + 1024 * j)):int64`;
    `word_add fp (word (4112 + 1024 * j)):int64`; `word (6 + 416 * j):int64`;
    `pc:num`] 52 THEN
  ARM_STEPS_TAC SI87_RIT_EXEC [53] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `j:num` SI87_RIT_LAST) (ASSUME `j < 8`)]) THEN
  SI87_CASES_TAC `j + 1 < 8` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES; ADD_ASSOC] THEN
      CONV_TAC WORD_RULE THEN NO_TAC) THEN
  SI87_END_TAC;;

let SI87_RIT = prove
 (SI87_RIT_STMT,
  MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n) (SI87_RIT_CALLEES ()) THEN
  CONCRETIZE_F_EVENTS_TAC SI87_RIT_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `ok1:bool`; `ok2:bool`; `sk:int64`;
                       `skb:num->byte`; `fp:int64`; `j:num`; `w:num->int32`;
                       `cphat:num->int32`; `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; fst SI87_RIT_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN SI87_ORIENT_TAC THEN
  FULL_INIT_TAC THEN
  SI87_RIT_PART1_TAC THEN SI87_RIT_PART2_TAC THEN SI87_RIT_PART3_TAC);;

(* ------------------------------------------------------------------------- *)
(* The loop over the rows of w0, for the first m rows, both of whose checks  *)
(* pass (RPRE), from the exit of the loop over z (loop43_exit1), where the   *)
(* code sets up row 0, as in the 44 stages: row j of w holds w0_j - c s2_j + *)
(* c t0_j afterwards (mld_sign_hint_x), the rows after the first m are       *)
(* unchanged.                                                                *)
(* ------------------------------------------------------------------------- *)

let SI87_ORR_THM k c =
  let tm = parse_term(Printf.sprintf
    "aligned 32 (fp:int64)
     ==> word_or (word_add fp (word %d)) (word %d) = word_add fp (word %d)" k c (k+c)) in
  prove(tm, REWRITE_TAC[MLD_WRAP_ALIGNED_16_32] THEN
            W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let SI87_ALIGNED16_32 = prove
 (`!x:int64. aligned 32 x ==> aligned 16 x`,
  REWRITE_TAC[MLD_WRAP_ALIGNED_16_32] THEN
  GEN_TAC THEN W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let SI87_RPRE_HX = list_mk_comb(`mld_sign_hint_x 8 mld_poly_decompose_lo_32`,
  [`w:num->int32`; SI87_S2H; SI87_T0H; `cphat:num->int32`]);;

let SI87_RPRE_STMT = parse_term(
 "exists f_events.
    forall e m sk skb fp w cphat pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 32 fp /\\ m <= 8 /\\
      (!j. j < m ==> mld_poly_chknorm (" ^ string_of_term SI87_RIT_R0 ^ ") (word 261768) =
                     word 0 /\\
                     mld_poly_chknorm (" ^ string_of_term SI87_RIT_CT0 ^ ") (word 261888) =
                     word 0) /\\
      ALL (nonoverlapping (word_sub fp (word 1472),16928))
          [(sk,4896); (word pc,libmldsa_size)]
      ==> ensures arm
           (\\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read PC s = word (pc + mldsa87_signature_internal_loop43_exit1) /\\
                read X22 s = word_add fp (word 1984) /\\\n" ^
  SI87_RIT_PRE ^ " /\\
                (!i. i < 2048 ==> read (memory :> bytes32 (word_add fp (word (4096 + 4 * i)))) s =
                                  mld_polyvec_map mld_poly_decompose_lo_32 w i) /\\
                read events s = e)
           (\\s. read PC s =
                (if m < 8 then word (pc + mldsa87_signature_internal_loop52)
                 else word (pc + mldsa87_signature_internal_loop52_exit1)) /\\
                read SP s = fp /\\
                read X25 s = word_add fp (word 1984) /\\ read X22 s = word_add fp (word 14448) /\\
                (0 < m ==> read X14 s = word 523777) /\\
                read X23 s = word m /\\ read X19 s = word (96 * m) /\\
                read X24 s = word_add fp (word (4096 + 1024 * m)) /\\
                read X0 s = word 2 /\\ " ^ SI87_PC245760 ^
 "              read (memory :> bytes64 (word_add fp (word 168))) s = word (6 + 416 * m) /\\
                read (memory :> bytes64 (word_add fp (word 208))) s =
                word_add fp (word (4112 + 1024 * m)) /\\
                (!i. i < 256 * m ==> read (memory :> bytes32 (word_add fp (word (4096 + 4 * i)))) s =
                                     " ^ string_of_term SI87_RPRE_HX ^ " i) /\\
                (!i. 256 * m <= i /\\ i < 2048
                     ==> read (memory :> bytes32 (word_add fp (word (4096 + 4 * i)))) s =
                         mld_polyvec_map mld_poly_decompose_lo_32 w i) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events m sk fp pc /\\
                   memaccess_inbounds e2
                    [sk,4896; word_sub fp (word 1472),16928;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa87_signature_internal_consts),400]
                    [word_sub fp (word 1472),16928]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [X18; X19; X20; X22; X23; X24; X25; X30] ,,
            MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
            MAYCHANGE [memory :> bytes(word_sub fp (word 208),208);
                       memory :> bytes(word_add fp (word 168),8);
                       memory :> bytes(word_add fp (word 208),8);
                       memory :> bytes(word_add fp (word 224),416);
                       memory :> bytes(word_add fp (word 4096),8192);
                       memory :> bytes(word_add fp (word 13312),1024)])");;

let SI87_RPRE_EXEC = SI87_EXEC_RANGE "loop43_exit1" "loop52_exit1";;

let SI87_RPRE_INV = parse_term(
 "\\i s. read X23 s = word i /\\ read X19 s = word (96 * i) /\\
        read X25 s = word_add fp (word 1984) /\\ read X22 s = word_add fp (word 14448) /\\
        (0 < i ==> read X14 s = word 523777) /\\
        read X24 s = word_add fp (word (4096 + 1024 * i)) /\\ " ^ SI87_PC245760 ^
 "      read (memory :> bytes64 (word_add fp (word 168))) s = word (6 + 416 * i) /\\
        read (memory :> bytes64 (word_add fp (word 208))) s =
        word_add fp (word (4112 + 1024 * i)) /\\\n" ^ SI87_RIT_PRE ^ " /\\
        (!k. k < 256 * i ==> read (memory :> bytes32 (word_add fp (word (4096 + 4 * k)))) s =
                             " ^ string_of_term SI87_RPRE_HX ^ " k) /\\
        (!k. 256 * i <= k /\\ k < 2048
             ==> read (memory :> bytes32 (word_add fp (word (4096 + 4 * k)))) s =
                 mld_polyvec_map mld_poly_decompose_lo_32 w k)");;

(*** The PC after row i of the first m <= 8 rows, from that of RIT ***)

let SI87_RPRE_PC = prove
 (`!i m a b. i < m /\ m <= 8
             ==> (if i + 1 < 8 then word a else word b):int64 =
                 word (if i + 1 < m then a else if m < 8 then a else b)`,
  REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMPLE_ARITH_TAC);;

(*** The setup of row 0 (18 instructions, the ADRPs at steps 10 to 16) ***)

let SI87_ADRP_STEPS_TAC exec ns =
  MAP_EVERY (fun n -> ARM_STEPS_TAC exec [n] THEN MLKEM_NATIVE_ADRP_TAC) ns;;

let SI87_RPRE_SETUP_TAC =
  ARM_STEPS_TAC SI87_RPRE_EXEC (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SI87_ORR_THM 4096 16) (ASSUME `aligned 32 (fp:int64)`)]) THEN
  SI87_ADRP_STEPS_TAC SI87_RPRE_EXEC (10--16) THEN
  ARM_STEPS_TAC SI87_RPRE_EXEC (17--18);;

let SI87_RPRE_ALLOWED = [`sk:int64`; `fp:int64`; `pc:num`; `i:num`];;

let SI87_LOOP_MEMACCESS_TAC =
  SIGN_BETA_ALL_TAC THEN SIGN_SPLIT_MEMACCESS_ASM_TAC THEN SI87_FB_NORM_TAC 1472 THEN
  REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

let SI87_LOOP_END_TAC =
  SIGN_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [SIGN_LOOP_UNIFY_TAC; SI87_LOOP_MEMACCESS_TAC];;

let SI87_RPRE_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `i < 8` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    can (term_match [] `!j. j < m ==> P j /\ Q j`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FULL_INIT_TAC THEN
  MP_TAC(SPECL [`fp:int64`; `4096`; `2048`; `mld_poly_decompose_lo_32`;
                `w:num->int32`; `i:num`; `s0:armstate`] SIGN_ROW_SLICE) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [`i:num`; `s0:armstate`]
             `!k. 256 * i <= k /\ k < 2048
                  ==> read (memory :> bytes32 (word_add fp (word (4096 + 4 * k)))) s0 = Q k`)
           (concl th)
    then REWRITE_TAC[th] else NO_TAC) THEN
  ANTS_TAC THENL [UNDISCH_TAC `i < 8` THEN ARITH_TAC; STRIP_TAC] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc SI87_RPRE_EXEC "H_RIT"
   [`T`; `T`; `sk:int64`; `skb:num->byte`; `fp:int64`; `i:num`; `w:num->int32`;
    `cphat:num->int32`; `pc:num`] SI87_RPRE_ALLOWED 1 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SI87_RPRE_PC
                               (CONJ (ASSUME `i < m`) (ASSUME `m <= 8`))]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SIGN_ROW_JOIN THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
  (SI87_MAYCHANGE_TAC ORELSE SI87_LOOP_END_TAC);;

let SI87_CLOSED_END_TAC =
  W(fun (asl,w) ->
    let _,bod = dest_exists w in
    match conjuncts bod with
      [_; eq; _] -> EXISTS_TAC (rhs eq)
    | _ -> failwith "SI87_CLOSED_END_TAC") THEN
  SIGN_BETA_ALL_TAC THEN REWRITE_TAC[ENUMERATEL; APPEND; APPEND_NIL] THEN
  REPEAT CONJ_TAC THEN
  TRY(ASM_REWRITE_TAC[APPEND; APPEND_NIL; GSYM APPEND_ASSOC] THEN NO_TAC) THEN
  SI87_FB_NORM_TAC 1472 THEN REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

let SI87_RPRE = prove
 (SI87_RPRE_STMT,
  SI87_ASSUME_CALLEE_TAILED_TAC SI87_RIT "H_RIT" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(m:num) (sk:int64) (fp:int64) (pc:num).
     APPEND (f_ev_back m sk fp pc)
      (APPEND (ENUMERATEL m (\i. f_ev_rit sk fp pc i)) (f_ev_front sk fp pc))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `m:num`; `sk:int64`; `skb:num->byte`;
    `fp:int64`; `w:num->int32`; `cphat:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst SI87_RPRE_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SI87_ALIGNED16_32) THEN
  ASM_CASES_TAC `0 < m` THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `m:num`
     `pc + mldsa87_signature_internal_loop52`
     `if m < 8 then pc + mldsa87_signature_internal_loop52
      else pc + mldsa87_signature_internal_loop52_exit1`
     SI87_RPRE_INV THEN
    REPEAT CONJ_TAC THENL
     [SIMPLE_ARITH_TAC;
      REWRITE_TAC[CONJUNCT1 LT; MULT_CLAUSES; ADD_CLAUSES; LE_0] THEN
      FULL_INIT_TAC THEN SI87_RPRE_SETUP_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN SI87_END_TAC;
      SI87_RPRE_BODY_TAC;
      REWRITE_TAC[] THEN FULL_INIT_TAC THEN SIGN_PC_COND_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      SIGN_BETA_ALL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC];
    SUBGOAL_THEN `m = 0` SUBST_ALL_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN SI87_RPRE_SETUP_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ARITH; MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    REWRITE_TAC[ENUMERATEL; APPEND; APPEND_NIL] THEN SI87_CLOSED_END_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The end of the product A y (HPOST), from loop3_exit to the NTT of the     *)
(* challenge, as in the 44 stages: the rows k of w at fp + 4096 + 1024 k are *)
(* mld_lazy_acc rho k y^ 6; the zeroing of the seed of the matrix, the       *)
(* reduction, the inverse NTT and caddq of each row (mld_sign_w, by          *)
(* MLD_LAZY_SIGN_W), the rolled decomposition of the rows with w0 in place   *)
(* and w1 packed at fp + 12288 (SI87_DW1R), c~ = SHAKE256(mu || w1) at       *)
(* fp + 14368 inlined (SI87_C2), the challenge at fp + 3072 and its NTT.     *)
(* ------------------------------------------------------------------------- *)

let SI87_YH = `mld_polyvec_map mld_poly_ntt (mld_sign_y mld_poly_uniform_gamma1_19 RHO (7 * att))`;;
let SI87_W = `mld_sign_w 7 (mld_polyvec_matrix_expand 7 rho)
               (mld_sign_y mld_poly_uniform_gamma1_19 RHO (7 * att))`;;
let SI87_W1 = mk_comb(`mld_sign_w1 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128`,SI87_W);;
let SI87_CT = mk_comb(`mld_sign_ctilde 8 128 MU`,SI87_W1);;
let SI87_CTN = mk_comb(`num_of_bytelist`,list_mk_comb(`list_of_seq:(num->byte)->num->byte list`,
                                                     [SI87_CT; `64`]));;

let SI87_SLOT_FACTS l = String.concat "" (map (fun (a,v) ->
  Printf.sprintf
   "read (memory :> bytes64 (word_add fp (word %d))) s = word_add fp (word %d) /\\\n" a v) l);;

let SI87_ACC_ROWS = String.concat "" (map (fun k -> Printf.sprintf
  "(!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (%d + 4 * i)))) s =
                   mld_lazy_acc rho %d (%s) 6 i) /\\\n" (4096 + 1024 * k) k
  (string_of_term SI87_YH)) (0--7));;

let SI87_HPOST_STMT = parse_term(
 "!mf ea el ev.
   memset_full_contract mf ea el ev
   ==> exists f_events.
        forall e fp rho RHO MU att C guard pc.
         aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
         aligned 32 fp /\\ att < 9361 /\\ mld_matrix_terminates 8 7 rho /\\
         " ^ string_of_term SI87_CTN ^ " = C /\\
         mld_poly_challenge_terminates 60 64 C /\\
         ALL (nonoverlapping (word_sub fp (word 1472),16928))
             [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8); (guard,8);
              (word(pc + got_memset),8); (ea,el)]
         ==> ensures arm
              (\\s. aligned_bytes_loaded s (word pc)
                     mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                   read PC s = word (pc + mldsa87_signature_internal_loop3_exit) /\\
                   read SP s = fp /\\
                   read X27 s = word_add fp (word 13312) /\\
                   read (memory :> bytes128 (word_add fp (word 192))) s =
                   word 339618401959998730991157055895298383871 /\\\n" ^
  SI87_SLOT_FACTS [144,11264; 152,10240; 160,9216] ^
  SI87_ACC_ROWS ^
 "                 read (memory :> bytes (word_add fp (word 1920),64)) s = MU /\\
                   read (memory :> bytes64(word(pc + got_stack_chk_guard))) s = guard /\\
                   read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                   read (memory :> bytes(ea,el)) s = ev /\\
                   read events s = e)
              (\\s. read PC s = word (pc + mldsa87_signature_internal_after_mldsa_poly_ntt_2) /\\
                   read SP s = fp /\\
                   read X21 s = word_add fp (word 14336) /\\
                   read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                   read (memory :> bytes(ea,el)) s = ev /\\
                   (!i. i < 2048 ==> read (memory :> bytes32 (word_add fp (word (4096 + 4 * i)))) s =
                                     mld_polyvec_map mld_poly_decompose_lo_32 (" ^
                                       string_of_term SI87_W ^ ") i) /\\
                   (!j. j < 1024 ==> read (memory :> bytes8 (word_add fp (word (12288 + j)))) s =
                                    " ^ string_of_term SI87_W1 ^ " j) /\\
                   read (memory :> bytes (word_add fp (word 14368),64)) s = C /\\
                   (!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (3072 + 4 * i)))) s =
                                    mld_sign_cphat 60 64 (" ^ string_of_term SI87_CT ^ ") i) /\\
                   (exists e2.
                      read events s = APPEND e2 e /\\
                      e2 = f_events fp guard mf pc C /\\
                      memaccess_inbounds e2
                       [word_sub fp (word 1472),16928;
                        word(pc + got_stack_chk_guard),8; guard,8;
                        word(pc + got_memset),8; ea,el;
                        word(pc + rodata_mld_KeccakF_RoundConstants),192;
                        word(pc + rodata_mld_zetas),1024;
                        word(pc + mldsa87_signature_internal_consts),400]
                       [word_sub fp (word 1472),16928]))
              (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [X18; X19; X20; X21; X23; X24; X30] ,,
               MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
               MAYCHANGE [memory :> bytes(word_sub fp (word 768),768);
                          memory :> bytes(word_add fp (word 400),240);
                          memory :> bytes(word_add fp (word 3072),1024);
                          memory :> bytes(word_add fp (word 4096),8192);
                          memory :> bytes(word_add fp (word 12288),1024);
                          memory :> bytes(word_add fp (word 13312),1024);
                          memory :> bytes(word_add fp (word 14368),64);
                          memory :> bytes(word_add fp (word 14752),208)])");;

let SI87_HPOST_EXEC = SI87_EXEC_RANGE "loop3_exit" "after_mldsa_poly_ntt_2";;

let SI87_HV = mk_comb(`mld_polyvec`,mk_abs(`i:num`,
  list_mk_comb(`mld_lazy_acc`,[`rho:num`; `i:num`; SI87_YH; `6`])));;
let SI87_HV1 = mk_comb(`mld_polyvec_map mld_poly_reduce`,SI87_HV);;
let SI87_HV2 = mk_comb(`mld_polyvec_map mld_poly_invntt_tomont`,SI87_HV1);;
let SI87_YVL = `mld_polyvec_matrix_yvec_lazy 7 rho
                 (mld_sign_y mld_poly_uniform_gamma1_19 RHO (7 * att))`;;
let SI87_HV3 = mk_comb(`mld_polyvec_map mld_poly_caddq`,SI87_YVL);;

let SI87_YVL_EQ = prove
 (mk_eq(SI87_YVL,SI87_HV2),
  REWRITE_TAC[mld_polyvec_matrix_yvec_lazy] THEN CONV_TAC NUM_REDUCE_CONV);;

let SI87_HPOLY v k = mk_comb(mk_comb(`mld_poly_of`,v),mk_small_numeral k);;

let SI87_WEQ = mk_forall(`j:num`,mk_imp(`j < 2048`,
  mk_eq(mk_comb(SI87_HV3,`j:num`),mk_comb(SI87_W,`j:num`))));;

let SI87_WEQ_TAC =
  SUBGOAL_THEN SI87_WEQ ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`8`; `7`; `rho:num`;
                  `mld_sign_y mld_poly_uniform_gamma1_19 RHO (7 * att)`; `j:num`]
                 MLD_LAZY_SIGN_W) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    ASM_REWRITE_TAC[MLD_LAZY_SIGN_Y_BOUND];
    ALL_TAC];;

let SI87_W_TAC k =
  let old = SI87_HPOLY SI87_HV3 k and nw = SI87_HPOLY SI87_W k in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_forall c && can (find_term ((=) old)) c then
      let iv,_ = dest_forall c in
      SUBGOAL_THEN (subst [nw,old] c) ASSUME_TAC THENL
       [X_GEN_TAC iv THEN DISCH_THEN(fun ith ->
          REWRITE_TAC[MP (SPEC iv th) ith] THEN REWRITE_TAC[mld_poly_of] THEN
          FIRST_ASSUM(fun wth -> if concl wth = SI87_WEQ then MATCH_MP_TAC wth
                                 else NO_TAC) THEN
          MP_TAC ith THEN ARITH_TAC);
        ALL_TAC]
    else NO_TAC);;

(*** Row k at fp + 4096 + 1024 k as the offset loops state it (base x19 =  ***)
(*** fp + 4096, or fp + 3072 for the reductions of rows 5 to 7), and back  ***)

let SI87_ROW_EQS = map (fun k ->
  prove(parse_term(Printf.sprintf
    "!i. word_add (word_add fp (word 4096)) (word (%d + 4 * i)):int64 =
         word_add fp (word (%d + 4 * i))" (1024 * k) (4096 + 1024 * k)),
   GEN_TAC THEN REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE)) (1--7);;

let SI87_ROW_EQS60 = map (fun k ->
  prove(parse_term(Printf.sprintf
    "!i. word_add (word_add fp (word 3072)) (word (%d + 4 * i)):int64 =
         word_add fp (word (%d + 4 * i))" (1024 * (k + 1)) (4096 + 1024 * k)),
   GEN_TAC THEN REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE)) (5--7);;

let SI87_NEST_GEN_TAC eqth k v =
  let pat = parse_term(Printf.sprintf "word_add fp (word (%d + 4 * i)):int64"
                                      (4096 + 1024 * k)) in
  FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) pat)) (concl th) &&
                           can (find_term ((=) v)) (concl th)
    then ASSUME_TAC(REWRITE_RULE[GSYM eqth] th) else NO_TAC);;

let SI87_NEST_TAC k v =
  if k >= 5 then SI87_NEST_GEN_TAC (el (k - 5) SI87_ROW_EQS60) k v
  else SI87_NEST_GEN_TAC (el (k - 1) SI87_ROW_EQS) k v;;

let SI87_CROW_EQS = map (fun k ->
  prove(parse_term(Printf.sprintf
    "!i. word_add fp (word (4096 + %d + 4 * i)):int64 = word_add fp (word (%d + 4 * i))"
    (1024 * k) (4096 + 1024 * k)),
   GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC)) (1--7);;

let SI87_CNEST_TAC k v =
  SI87_NEST_GEN_TAC (el (k - 1) SI87_CROW_EQS) k v;;

let SI87_ASM_RW_TAC ths =
  RULE_ASSUM_TAC(fun th ->
    if can (find_term (fun t -> is_const t && fst(dest_const t) = "ensures")) (concl th)
    then th else REWRITE_RULE ths th);;

let SI87_FLAT_TAC = SI87_ASM_RW_TAC (SI87_ROW_EQS @ SI87_ROW_EQS60 @ SI87_CROW_EQS);;

let SI87_HCALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc SI87_HPOST_EXEC
    name ilist [`fp:int64`; `guard:int64`; `mf:int64`; `pc:num`; `C:num`] n;;

let SI87_FPK k = parse_term(Printf.sprintf "word_add fp (word %d):int64" (4096 + 1024 * k));;

let SI87_REPOLY_MAP_TAC f v1 v2 k =
  MLD_LAZY_REPOLY_TAC (mk_comb(f,SI87_HPOLY v1 k)) (SI87_HPOLY v2 k)
    [MLD_POLY_OF_POLYVEC_MAP];;

let SI87_HPOST_CALLEES ms =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    (MATCH_MP MLDSA_NATIVE_POLY_CHALLENGE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL ms)
    "H_CHAL" THEN
  MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
   ([MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_NTT";
     MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_INV";
     SI87_DW1R,"H_DW1R"; SI87_C2,"H_C2"] @
    map (fun k -> SI87_LK SI87_RED ("loop" ^ string_of_int (22 + k)),
                  "H_RED" ^ string_of_int k) (0--7) @
    map (fun k -> SI87_LK SI87_CADDQ ("loop" ^ string_of_int (30 + k)),
                  "H_CADDQ" ^ string_of_int k) (0--7));;

let SI87_HPOST_RED_TAC k n =
  (if k = 0 then ALL_TAC else SI87_NEST_TAC k (SI87_HPOLY SI87_HV k)) THEN
  SI87_HCALL_TAC ("H_RED" ^ string_of_int k)
    [(if k >= 5 then `word_add fp (word 3072):int64` else SI87_FPK 0);
     SI87_HPOLY SI87_HV k; `pc:num`] n THEN SI87_FLAT_TAC THEN
  SI87_REPOLY_MAP_TAC `mld_poly_reduce` SI87_HV SI87_HV1 k;;

let SI87_HPOST_INV_TAC k n =
  SI87_HCALL_TAC "H_INV" [`read X0 s`; SI87_HPOLY SI87_HV1 k; `pc:num`;
                          `read SP s`; `read X30 s`] n THEN
  SI87_REPOLY_MAP_TAC `mld_poly_invntt_tomont` SI87_HV1 SI87_HV2 k;;

let SI87_HPOST_CADDQ_TAC k n =
  (if k = 0 then ALL_TAC else SI87_CNEST_TAC k (SI87_HPOLY SI87_YVL k)) THEN
  SI87_HCALL_TAC ("H_CADDQ" ^ string_of_int k) [SI87_FPK 0; SI87_HPOLY SI87_YVL k; `pc:num`] n THEN
  SI87_FLAT_TAC THEN
  SI87_REPOLY_MAP_TAC `mld_poly_caddq` SI87_YVL SI87_HV3 k THEN SI87_W_TAC k;;

let SI87_HPOST_PART1_TAC =
  MAP_EVERY (fun k -> TRY(MLD_LAZY_REPOLY_TAC
     (list_mk_comb(`mld_lazy_acc`,[`rho:num`; mk_small_numeral k; SI87_YH; `6`]))
     (SI87_HPOLY SI87_HV k) [MLD_POLY_OF_POLYVEC])) (0--7) THEN
  ARM_STEPS_TAC SI87_HPOST_EXEC (1--11) THEN SI87_HPOST_RED_TAC 0 12 THEN
  MAP_EVERY (fun k -> ARM_STEPS_TAC SI87_HPOST_EXEC [11 + 2 * k] THEN
                      SI87_HPOST_RED_TAC k (12 + 2 * k)) (1--7) THEN
  ARM_STEPS_TAC SI87_HPOST_EXEC (27--28) THEN SI87_HPOST_INV_TAC 0 29 THEN
  MAP_EVERY (fun k -> ARM_STEPS_TAC SI87_HPOST_EXEC [27 + 3 * k; 28 + 3 * k] THEN
                      SI87_HPOST_INV_TAC k (29 + 3 * k)) (1--7) THEN
  SI87_ASM_RW_TAC[GSYM SI87_YVL_EQ] THEN
  ARM_STEPS_TAC SI87_HPOST_EXEC (51--53) THEN SI87_HPOST_CADDQ_TAC 0 54 THEN
  SI87_HPOST_CADDQ_TAC 1 55 THEN SI87_HPOST_CADDQ_TAC 2 56 THEN
  SI87_HPOST_CADDQ_TAC 3 57 THEN ARM_STEPS_TAC SI87_HPOST_EXEC [58] THEN
  SI87_HPOST_CADDQ_TAC 4 59 THEN SI87_HPOST_CADDQ_TAC 5 60 THEN
  SI87_HPOST_CADDQ_TAC 6 61 THEN ARM_STEPS_TAC SI87_HPOST_EXEC [62] THEN
  SI87_HPOST_CADDQ_TAC 7 63;;

let SI87_HPOST_SETUP_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(fun ms -> SI87_HPOST_CALLEES ms) THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(fp:int64) (guard:int64) (mf:int64) (pc:num) (C:num).
      f_ev_hpost fp guard mf pc C:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `fp:int64`; `rho:num`; `RHO:num`; `MU:num`;
                       `att:num`; `C:num`; `guard:int64`; `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; fst SI87_HPOST_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SI87_ALIGNED16_32) THEN
  SI87_WEQ_TAC THEN
  FULL_INIT_TAC;;

(*** The eight rows of w joined into the vector ***)

let SI87_ROWS_JOIN = prove
 (`!(f:num->int32) (fp:int64) (s:armstate).
     (!k. k < 8
          ==> !i. i < 256 ==> read (memory :> bytes32 (word_add fp (word ((4096 + 1024 * k) + 4 * i)))) s =
                              f (256 * k + i))
     ==> !i. i < 2048 ==> read (memory :> bytes32 (word_add fp (word (4096 + 4 * i)))) s = f i`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?k j. k < 8 /\ j < 256 /\ i = 256 * k + j` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC [`i DIV 256`; `i MOD 256`] THEN
    MP_TAC(SPECL [`i:num`; `256`] DIVISION) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `4096 + 4 * (256 * k + j) = (4096 + 1024 * k) + 4 * j`] THEN
  ASM_SIMP_TAC[]);;

let SI87_CT_EQ = prove
 (`!MU (W:num->byte).
     mld_shake256_byte 1088 (MU + 2 EXP 512 * num_of_bytelist(list_of_seq W 1024)) =
     mld_sign_ctilde 8 128 MU W`,
  REWRITE_TAC[mld_sign_ctilde] THEN CONV_TAC NUM_REDUCE_CONV);;

let SI87_W1N = mk_comb(`num_of_bytelist`,list_mk_comb(`list_of_seq:(num->byte)->num->byte list`,
                                                     [SI87_W1; `1024`]));;

let SI87_HPOST_PART2_TAC =
  ARM_STEPS_TAC SI87_HPOST_EXEC (64--76) THEN
  (*** the rows of w as the vector for DW1R ***)
  RULE_ASSUM_TAC(fun th -> let c = concl th in
    if is_forall c && can (find_term ((=) SI87_W)) c &&
       not(can (find_term (fun t -> is_const t && fst(dest_const t) = "ensures")) c)
    then CONV_RULE(NUM_REDUCE_CONV THENC REWRITE_CONV[ADD_CLAUSES]) (REWRITE_RULE[mld_poly_of] th)
    else th) THEN
  SUBGOAL_THEN (subst [`s76:armstate`,`s:armstate`] (parse_term(
    "!i. i < 2048 ==> read (memory :> bytes32 (word_add fp (word (4096 + 4 * i)))) s =
                      " ^ string_of_term SI87_W ^ " i")))
   ASSUME_TAC THENL
   [MATCH_MP_TAC SI87_ROWS_JOIN THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  SI87_HCALL_TAC "H_DW1R" [`fp:int64`; SI87_W; `pc:num`] 77 THEN
  MP_TAC(SPECL [`fp:int64`; `12288`; `1024`; SI87_W1; `s77:armstate`]
               SIGN_READ_BYTES_OF_BYTES8_OFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SI87_HCALL_TAC "H_C2" [`fp:int64`; `MU:num`; SI87_W1N; `pc:num`] 78 THEN
  SI87_ASM_RW_TAC[SI87_CT_EQ] THEN
  SI87_ASM_RW_TAC[ASSUME (mk_eq(SI87_CTN,`C:num`))] THEN
  ARM_STEPS_TAC SI87_HPOST_EXEC [79] THEN
  SI87_HCALL_TAC "H_CHAL" [`read X0 s`; `read X1 s`; `C:num`; `guard:int64`; `pc:num`;
     `read SP s`; `read X30 s`] 80 THEN
  ARM_STEPS_TAC SI87_HPOST_EXEC (81--82) THEN
  SI87_HCALL_TAC "H_NTT" [`read X0 s`; `mld_poly_challenge 60 64 C`;
     `pc:num`; `read SP s`; `read X30 s`] 83 THEN
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_forall c && can (find_term ((=) `mld_poly_challenge 60 64 C`)) c &&
       not(can (find_term (fun t -> is_const t && fst(dest_const t) = "ensures")) c)
    then REWRITE_RULE[GSYM mld_sign_cphat]
           (REWRITE_RULE[SYM(ASSUME (mk_eq(SI87_CTN,`C:num`)))] th)
    else th) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SI87_END_TAC;;

let SI87_HPOST = prove
 (SI87_HPOST_STMT,
  SI87_HPOST_SETUP_TAC THEN SI87_HPOST_PART1_TAC THEN SI87_HPOST_PART2_TAC);;

(* ------------------------------------------------------------------------- *)
(* A column of the loop over y (YCOL), from loop3 with the column j in w19:  *)
(* y_j sampled (the inlined poly_uniform_gamma1, nonce 7 att + j) at         *)
(* fp + 13312 and transformed, then for each row i the entry (i,j) of the    *)
(* matrix sampled by poly_uniform from the seed rho || j || i at fp + 14368. *)
(* For j > 0 (SI87_YCOLJ, j = n + 1) its product with y^_j at fp + 736 is    *)
(* added to row i; for j = 0 (SI87_YCOL0) the entry is sampled into row i    *)
(* and multiplied in place. Row i then holds mld_lazy_acc rho i y^ j.        *)
(* ------------------------------------------------------------------------- *)

let SI87_SEED = prove
 (`!fp rho i j (s:armstate).
     read (memory :> bytes(word_add fp (word 14368),32)) s = rho /\
     read (memory :> bytes8 (word_add fp (word 14400))) s = word j /\
     read (memory :> bytes8 (word_add fp (word 14401))) s = word i /\
     i < 256 /\ j < 256
     ==> read (memory :> bytes(word_add fp (word 14368),34)) s = mld_matrix_seed rho i j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mld_matrix_seed] THEN
  REWRITE_TAC[ARITH_RULE `34 = 32 + 1 + 1`; READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  CONV_TAC(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[READ_MEMORY_BYTES_BYTES8] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC);;

let SI87_ACC_SUC = prove
 (`!rho i (v:num->int32) n.
     mld_lazy_acc rho i v (n + 1) =
     mld_poly_add (mld_lazy_acc rho i v n)
      (mld_poly_pointwise_montgomery (mld_poly_uniform (mld_matrix_seed rho i (n + 1)))
                                     (mld_poly_of v (n + 1)))`,
  REWRITE_TAC[GSYM ADD1; mld_lazy_acc; mld_matrix_entry]);;

let SI87_YCOL_PRE =
 "read SP s = fp /\\
  read X22 s = word_add fp (word 14448) /\\ read X27 s = word_add fp (word 13312) /\\
  read X25 s = word_add fp (word 1984) /\\
  read X28 s = word 18446744073701171199 /\\ read X26 s = word 252236767799803904 /\\
  read Q7 s = word 0 /\\
  read (memory :> bytes64 (word_add fp (word 216))) s = word_add fp (word 14761) /\\
  read (memory :> bytes32 (word_add fp (word 624))) s = word (7 * att) /\\\n" ^
  SI87_SLOT_FACTS [112,11276; 120,10252; 128,9228; 136,8204;
                   144,11264; 152,10240; 160,9216] ^
 "read (memory :> bytes (word_add fp (word 1984),64)) s = RHO /\\
  read (memory :> bytes (word_add fp (word 14368),32)) s = rho /\\
  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s = guard /\\
  read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
  read (memory :> bytes(ea,el)) s = ev";;

let SI87_YCOL_POST =
 "read SP s = fp /\\
  read X22 s = word_add fp (word 14448) /\\ read X27 s = word_add fp (word 13312) /\\
  read Q7 s = word 0 /\\\n";;

let SI87_ACC_ROWS_N n = String.concat " /\\\n" (map (fun k -> Printf.sprintf
  "(!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (%d + 4 * i)))) s =
                   mld_lazy_acc rho %d (%s) %s i)" (4096 + 1024 * k) k
  (string_of_term SI87_YH) n) (0--7));;

let SI87_YCOL_READS =
 "[word_sub fp (word 1472),16928;
   word(pc + got_stack_chk_guard),8; guard,8;
   word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
   word(pc + rodata_mld_KeccakF_RoundConstants),192;
   word(pc + rodata_mld_zetas),1024;
   word(pc + mldsa87_signature_internal_consts),400]
  [word_sub fp (word 1472),16928]";;

let SI87_YCOL_MAYCHANGE =
 "(MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
   MAYCHANGE [X18; X19; X20; X21; X22; X23; X24; X30] ,,
   MAYCHANGE [memory :> bytes(word_sub fp (word 1472),1472);
              memory :> bytes(word_add fp (word 736),1024);
              memory :> bytes(word_add fp (word 4096),8192);
              memory :> bytes(word_add fp (word 13312),1024);
              memory :> bytes(word_add fp (word 14400),2);
              memory :> bytes(word_add fp (word 14448),984)])";;

let SI87_YCOLJ_STMT = parse_term(
 "!mf mc ea el ev.
   memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
   ==> exists f_events.
        forall e fp rho RHO att n guard pc.
         aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
         aligned 32 fp /\\ att < 9361 /\\ n < 6 /\\ mld_matrix_terminates 8 7 rho /\\
         ALL (nonoverlapping (word_sub fp (word 1472),16928))
             [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8); (guard,8);
              (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
         ==> ensures arm
              (\\s. aligned_bytes_loaded s (word pc)
                     mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                   read PC s = word (pc + mldsa87_signature_internal_loop3) /\\
                   read X19 s = word (n + 1) /\\\n" ^ SI87_YCOL_PRE ^ " /\\\n" ^
  SI87_ACC_ROWS_N "n" ^ " /\\
                   read events s = e)
              (\\s. read PC s = (if n + 2 < 7 then word (pc + mldsa87_signature_internal_loop3)
                                else word (pc + mldsa87_signature_internal_loop3_exit)) /\\
                   read X19 s = word (n + 2) /\\\n" ^ SI87_YCOL_POST ^
  SI87_ACC_ROWS_N "(n + 1)" ^ " /\\
                   (exists e2.
                      read events s = APPEND e2 e /\\
                      e2 = f_events fp rho n guard mf mc pc /\\
                      memaccess_inbounds e2 " ^ SI87_YCOL_READS ^ "))
              " ^ SI87_YCOL_MAYCHANGE);;

let SI87_YCOL_EXEC = SI87_EXEC_RANGE "join3" "loop3_exit";;

let SI87_ZX8 = prove
 (`!k. k < 256 ==> word_zx (word k:int64):byte = word k`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `k MOD 256 = k /\ k MOD 18446744073709551616 = k` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_REWRITE_TAC[]]);;

let SI87_COLNZ = prove
 (`!n. n < 6 ==> ~(val (word_zx (word (n + 1):int64):int32) = 0)`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let SI87_ZX_BYTE = prove
 (`!n. word_zx (word_zx (word n:int64):int32):byte = word n`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_32;
              DIMINDEX_64] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

let SI87_PU_PRE_TAC i jt st =
  MP_TAC(SPECL [`fp:int64`; `rho:num`; mk_small_numeral i; jt; st] SI87_SEED) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `n + 1 < 256` ASSUME_TAC THENL
     [UNDISCH_TAC `n < 6` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SI87_ZX_BYTE; SI87_ZX8] THEN UNDISCH_TAC `n < 6` THEN ARITH_TAC;
    DISCH_TAC] THEN
  FIRST_ASSUM(fun th -> if can (term_match [] `mld_matrix_terminates 8 7 r`) (concl th) then
    MP_TAC(SPECL [mk_small_numeral i; jt] (REWRITE_RULE[mld_matrix_terminates] th)) THEN
    ANTS_TAC THENL [UNDISCH_TAC `n < 6` THEN ARITH_TAC; DISCH_TAC] else NO_TAC);;

let SI87_YCOL_ALLOWED = [`fp:int64`; `rho:num`; `n:num`; `guard:int64`; `mf:int64`;
                         `mc:int64`; `pc:num`];;

let SI87_YCOL_CALL_TAC name ilist k =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc SI87_YCOL_EXEC name
    ilist SI87_YCOL_ALLOWED k;;

let SI87_YY k = mk_comb(mk_comb(`mld_poly_of`,
  `mld_sign_y mld_poly_uniform_gamma1_19 RHO (7 * att)`),k);;
let SI87_YHK k = mk_comb(mk_comb(`mld_poly_of`,SI87_YH),k);;
let SI87_ACC i nt = list_mk_comb(`mld_lazy_acc`,[`rho:num`; mk_small_numeral i; SI87_YH; nt]);;
let SI87_ENT i jt = mk_comb(`mld_poly_uniform`,
  list_mk_comb(`mld_matrix_seed`,[`rho:num`; mk_small_numeral i; jt]));;
let SI87_PWT i jt = list_mk_comb(`mld_poly_pointwise_montgomery`,[SI87_ENT i jt; SI87_YHK jt]);;

(*** The frame of the inlined poly_uniform_gamma1 (fr = fp - 240) in the    ***)
(*** forms of fp                                                            ***)

let SI87_FR_EQS =
  map (fun k ->
    let tm = if k = 240 then `word_add (word_sub fp (word 240)) (word 240):int64 = fp`
      else parse_term(Printf.sprintf
        "word_add (word_sub fp (word 240)) (word %d):int64 = word_add fp (word %d)"
        k (k - 240)) in
    WORD_RULE tm) [240; 864; 14688; 456; 15001; 13552; 976; 14896; 14992] @
  map (fun k ->
    prove(parse_term(Printf.sprintf
      "!t. word_add (word_sub fp (word 240)) (word (%d + t)):int64 =
           word_add fp (word (%d + t))" k (k - 240)),
     GEN_TAC THEN REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE)) [13552; 14688; 14896; 14992];;

(*** The callees of a column ***)

let SI87_YCOL_CALLEES th =
  ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP SI87_G1_Y th) "H_G1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    (MATCH_MP MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL th)
    "H_PU" THEN
  MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
   ([MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_NTT"] @
    map (fun k -> SI87_LK SI87_PWM ("loop" ^ string_of_int (6 + k)),
                  "H_PWM" ^ string_of_int k) (0--7) @
    map (fun k -> el k SI87_ADDS, "H_ADD" ^ string_of_int k) (0--7) @
    map (fun k -> SI87_LK SI87_PWM ("loop" ^ string_of_int (14 + k)),
                  "H_PWMZ" ^ string_of_int k) (0--7));;

(*** y_j (index jt, nonce 7 att + jt) and its NTT, up to the branch on j ***)

let SI87_YCOL_Y_TAC jt =
  MAP_EVERY ASSUME_TAC SI87_FR_EQS THEN
  SI87_YCOL_CALL_TAC "H_G1" [`word_add fp (word 1984):int64`; `RHO:num`; `7 * att`; jt;
    `word_sub fp (word 240):int64`; `pc:num`] 1 THEN
  SI87_ASM_RW_TAC SI87_FR_EQS THEN
  MLD_LAZY_REPOLY_TAC
    (list_mk_comb(`mld_poly_uniform_gamma1_19`,
      [`RHO:num`; mk_comb(`word:num->int16`,mk_binop `(+):num->num->num` `7 * att` jt)]))
    (SI87_YY jt) [mld_sign_y; MLD_POLY_OF_POLYVEC] THEN
  ARM_STEPS_TAC SI87_YCOL_EXEC (2--16) THEN
  SI87_YCOL_CALL_TAC "H_NTT" [`read X0 s`; SI87_YY jt; `pc:num`; `read SP s`;
                              `read X30 s`] 17 THEN
  MLD_LAZY_REPOLY_TAC (mk_comb(`mld_poly_ntt`,SI87_YY jt)) (SI87_YHK jt)
    [MLD_POLY_OF_POLYVEC_MAP] THEN
  ARM_STEPS_TAC SI87_YCOL_EXEC (18--19) THEN
  SI87_ASM_RW_TAC[MP (SI87_ORR_THM 13312 8) (ASSUME `aligned 32 (fp:int64)`)] THEN
  ARM_STEPS_TAC SI87_YCOL_EXEC (20--21);;

(*** Row i of a column j > 0, the call of poly_uniform being step n0 ***)

let SI87_YCOLJ_ROW_TAC i n0 =
  let jt = `n + 1` in
  ARM_STEPS_TAC SI87_YCOL_EXEC [n0 - 1] THEN
  SI87_PU_PRE_TAC i jt (mk_var("s"^string_of_int (n0-1),`:armstate`)) THEN
  SI87_YCOL_CALL_TAC "H_PU" [`read X0 s`; `read X1 s`;
    list_mk_comb(`mld_matrix_seed`,[`rho:num`; mk_small_numeral i; jt]);
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] n0 THEN
  ARM_STEPS_TAC SI87_YCOL_EXEC [n0 + 1] THEN
  SI87_YCOL_CALL_TAC ("H_PWM" ^ string_of_int i)
    [`word_add fp (word 736):int64`; `word_add fp (word 13312):int64`;
     SI87_ENT i jt; SI87_YHK jt; `pc:num`] (n0 + 2) THEN
  SI87_YCOL_CALL_TAC ("H_ADD" ^ string_of_int i)
    ([`fp:int64`; SI87_ACC i `n:num`; SI87_PWT i jt] @
     (if i < 7 then [jt] else []) @ [`pc:num`]) (n0 + 3) THEN
  SI87_ASM_RW_TAC[GSYM SI87_ACC_SUC];;

let SI87_COLINC = prove
 (`!n. n < 6
       ==> word_zx (word_add (word_zx (word (n + 1):int64):int32) (word 1)):int64 =
           word (n + 2)`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV);;

let SI87_COLTEST = prove
 (`!n. n < 6
       ==> (val (word_sub (word_zx (word (n + 2):int64):int32) (word 7)) = 0 <=>
            ~(n + 2 < 7))`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let SI87_YCOLJ = prove
 (SI87_YCOLJ_STMT,
  REPEAT GEN_TAC THEN DISCH_THEN SI87_YCOL_CALLEES THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(fp:int64) (rho:num) (n:num) (guard:int64) (mf:int64) (mc:int64) (pc:num).
      if n + 2 < 7 then f_ev_mid fp rho n guard mf mc pc
      else f_ev_last fp rho n guard mf mc pc:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `fp:int64`; `rho:num`; `RHO:num`; `att:num`;
                       `n:num`; `guard:int64`; `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; fst SI87_YCOL_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SI87_ALIGNED16_32) THEN
  FULL_INIT_TAC THEN SI87_YCOL_Y_TAC `n + 1` THEN
  SI87_ASM_RW_TAC[MP (SPEC `n:num` SI87_COLNZ) (ASSUME `n < 6`)] THEN
  ARM_STEPS_TAC SI87_YCOL_EXEC (22--26) THEN
  MAP_EVERY (fun i -> SI87_YCOLJ_ROW_TAC i (28 + 5 * i)) (0--7) THEN
  ARM_STEPS_TAC SI87_YCOL_EXEC (67--71) THEN
  SI87_ASM_RW_TAC[MP (SPEC `n:num` SI87_COLINC) (ASSUME `n < 6`)] THEN
  SI87_ASM_RW_TAC[MP (SPEC `n:num` SI87_COLTEST) (ASSUME `n < 6`)] THEN
  SI87_CASES_TAC `n + 2 < 7` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SI87_END_TAC);;

(*** The column j = 0 ***)

let SI87_YCOL0_STMT = parse_term(
 "!mf mc ea el ev.
   memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
   ==> exists f_events.
        forall e fp rho RHO att guard pc.
         aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
         aligned 32 fp /\\ att < 9361 /\\ mld_matrix_terminates 8 7 rho /\\
         ALL (nonoverlapping (word_sub fp (word 1472),16928))
             [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8); (guard,8);
              (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
         ==> ensures arm
              (\\s. aligned_bytes_loaded s (word pc)
                     mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                   read PC s = word (pc + mldsa87_signature_internal_loop3) /\\
                   read X19 s = word 0 /\\\n" ^ SI87_YCOL_PRE ^ " /\\
                   read events s = e)
              (\\s. read PC s = word (pc + mldsa87_signature_internal_loop3) /\\
                   read X19 s = word 1 /\\\n" ^ SI87_YCOL_POST ^
  SI87_ACC_ROWS_N "0" ^ " /\\
                   (exists e2.
                      read events s = APPEND e2 e /\\
                      e2 = f_events fp rho guard mf mc pc /\\
                      memaccess_inbounds e2 " ^ SI87_YCOL_READS ^ "))
              " ^ SI87_YCOL_MAYCHANGE);;

(*** The seed from the 16-bit index j + 256 i stored by strh ***)

let SI87_SEED16 = prove
 (`!fp rho i (s:armstate).
     read (memory :> bytes(word_add fp (word 14368),32)) s = rho /\
     read (memory :> bytes16 (word_add fp (word 14400))) s = word (256 * i) /\
     i < 256
     ==> read (memory :> bytes(word_add fp (word 14368),34)) s = mld_matrix_seed rho i 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mld_matrix_seed] THEN
  REWRITE_TAC[ARITH_RULE `34 = 32 + 2`; READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  CONV_TAC(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `read (memory :> bytes(word_add fp (word 14400),2)) s = val(word (256 * i):int16)`
   SUBST1_TAC THENL
   [FIRST_X_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes16 a) s = x`) (concl th)
      then REWRITE_TAC[GSYM th] else NO_TAC) THEN
    REWRITE_TAC[BYTES16_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES; DIMINDEX_16] THEN
    CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[VAL_WORD; DIMINDEX_16] THEN
    SUBGOAL_THEN `(256 * i) MOD 2 EXP 16 = 256 * i` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ARITH_TAC]]);;

let SI87_PU0_PRE_TAC i st =
  MP_TAC(SPECL [`fp:int64`; `rho:num`; mk_small_numeral i; st] SI87_SEED16) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    TRY(FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes16 a) s = x`) (concl th)
                              then REWRITE_TAC[th] THEN CONV_TAC WORD_REDUCE_CONV else NO_TAC));
    DISCH_TAC] THEN
  FIRST_ASSUM(fun th -> if can (term_match [] `mld_matrix_terminates 8 7 r`) (concl th) then
    MP_TAC(SPECL [mk_small_numeral i; `0`] (REWRITE_RULE[mld_matrix_terminates] th)) THEN
    ANTS_TAC THENL [ARITH_TAC; DISCH_TAC] else NO_TAC);;

let SI87_ACC0 = prove
 (`!rho i (v:num->int32).
     mld_lazy_acc rho i v 0 =
     mld_poly_pointwise_montgomery (mld_poly_uniform (mld_matrix_seed rho i 0))
                                   (mld_poly_of v 0)`,
  REWRITE_TAC[mld_lazy_acc; mld_matrix_entry]);;

let SI87_YCOL0_ROW_TAC i n0 =
  (if i = 0 then ALL_TAC else
     ARM_STEPS_TAC SI87_YCOL_EXEC ((n0 - 6)--(n0 - 1)) THEN
     SI87_PU0_PRE_TAC i (mk_var("s"^string_of_int (n0-1),`:armstate`))) THEN
  SI87_YCOL_CALL_TAC "H_PU" [`read X0 s`; `read X1 s`;
    list_mk_comb(`mld_matrix_seed`,[`rho:num`; mk_small_numeral i; `0`]);
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] n0 THEN
  (if i = 0 then ARM_STEPS_TAC SI87_YCOL_EXEC ((n0+1)--(n0+4)) THEN
     SI87_ASM_RW_TAC[MP (SI87_ORR_THM 13312 8) (ASSUME `aligned 32 (fp:int64)`);
                     MP (SI87_ORR_THM 4096 8) (ASSUME `aligned 32 (fp:int64)`)]
   else ARM_STEPS_TAC SI87_YCOL_EXEC ((n0+1)--(n0+3)) THEN
     SI87_ASM_RW_TAC[MP (SI87_ORR_THM 13312 8) (ASSUME `aligned 32 (fp:int64)`)]) THEN
  SI87_YCOL_CALL_TAC ("H_PWMZ" ^ string_of_int i)
    [SI87_FPK i; `word_add fp (word 13312):int64`; SI87_ENT i `0`; SI87_YHK `0`; `pc:num`]
    (if i = 0 then n0 + 5 else n0 + 4) THEN
  SI87_ASM_RW_TAC[GSYM SI87_ACC0];;

let SI87_YCOL0 = prove
 (SI87_YCOL0_STMT,
  REPEAT GEN_TAC THEN DISCH_THEN SI87_YCOL_CALLEES THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(fp:int64) (rho:num) (guard:int64) (mf:int64) (mc:int64) (pc:num).
      f_ev_col0 fp rho guard mf mc pc:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `fp:int64`; `rho:num`; `RHO:num`; `att:num`;
                       `guard:int64`; `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; fst SI87_YCOL_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SI87_ALIGNED16_32) THEN
  FULL_INIT_TAC THEN SI87_YCOL_Y_TAC `0` THEN
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read PC s = x`) (concl th) then
     CONV_RULE(DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV) th else th) THEN
  ARM_STEPS_TAC SI87_YCOL_EXEC (22--26) THEN SI87_PU0_PRE_TAC 0 `s26:armstate` THEN
  SI87_YCOL0_ROW_TAC 0 27 THEN
  MAP_EVERY (fun i -> SI87_YCOL0_ROW_TAC i (28 + 11 * i)) (1--7) THEN
  ARM_STEPS_TAC SI87_YCOL_EXEC (110--114) THEN
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read PC s = x`) (concl th) ||
                              can (term_match [] `read X19 s = x`) (concl th) then
     CONV_RULE(DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV) th else th) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SI87_END_TAC);;

(* ------------------------------------------------------------------------- *)
(* The start of an attempt (HEAD), from loop2 with its number att in w9: att *)
(* saved at fp + 100, kappa = 7 att at fp + 624 (32 bits) and fp + 14344    *)
(* (16 bits), the pointer to rho'' at fp + 14336, rho copied from fp + 1760 *)
(* to the seed of the matrix at fp + 14368, then the seven columns of the    *)
(* product with the matrix (YCOL0, YCOLJ for n = 0 .. 5) and HPOST, to after *)
(* the NTT of the challenge, as in the 44 stages.                            *)
(* ------------------------------------------------------------------------- *)

let SI87_HEAD_PRE =
 "read SP s = fp /\\
  read X21 s = word_add fp (word 14336) /\\
  read X22 s = word_add fp (word 14448) /\\ read X27 s = word_add fp (word 13312) /\\
  read X25 s = word_add fp (word 1984) /\\
  read X28 s = word 18446744073701171199 /\\ read X26 s = word 252236767799803904 /\\
  read Q7 s = word 0 /\\
  read (memory :> bytes64 (word_add fp (word 80))) s = word_add fp (word 1760) /\\
  read (memory :> bytes64 (word_add fp (word 216))) s = word_add fp (word 14761) /\\
  read (memory :> bytes128 (word_add fp (word 192))) s =
  word 339618401959998730991157055895298383871 /\\\n" ^
  SI87_SLOT_FACTS [112,11276; 120,10252; 128,9228; 136,8204;
                   144,11264; 152,10240; 160,9216] ^
 "read (memory :> bytes (word_add fp (word 1760),32)) s = rho /\\
  read (memory :> bytes (word_add fp (word 1920),64)) s = MU /\\
  read (memory :> bytes (word_add fp (word 1984),64)) s = RHO /\\
  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s = guard /\\
  read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
  read (memory :> bytes(ea,el)) s = ev";;

let SI87_HEAD_STMT = parse_term(
 "!mf mc ea el ev.
   memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
   ==> exists f_events.
        forall e fp att rho RHO MU C guard pc.
         aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
         aligned 32 fp /\\ att < 9361 /\\ mld_matrix_terminates 8 7 rho /\\
         " ^ string_of_term SI87_CTN ^ " = C /\\
         mld_poly_challenge_terminates 60 64 C /\\
         ALL (nonoverlapping (word_sub fp (word 1472),16928))
             [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8); (guard,8);
              (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
         ==> ensures arm
              (\\s. aligned_bytes_loaded s (word pc)
                     mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                   read PC s = word (pc + mldsa87_signature_internal_loop2) /\\
                   read X9 s = word att /\\\n" ^ SI87_HEAD_PRE ^ " /\\
                   read events s = e)
              (\\s. read PC s = word (pc + mldsa87_signature_internal_after_mldsa_poly_ntt_2) /\\
                   read SP s = fp /\\
                   read X21 s = word_add fp (word 14336) /\\
                   read X22 s = word_add fp (word 14448) /\\
                   read X25 s = word_add fp (word 1984) /\\
                   read (memory :> bytes32 (word_add fp (word 100))) s = word att /\\
                   read (memory :> bytes64 (word_add fp (word 14336))) s =
                     word_add fp (word 1984) /\\
                   read (memory :> bytes16 (word_add fp (word 14344))) s =
                     word (7 * att) /\\
                   (!i. i < 2048 ==> read (memory :> bytes32 (word_add fp (word (4096 + 4 * i)))) s =
                                     mld_polyvec_map mld_poly_decompose_lo_32 (" ^
                                       string_of_term SI87_W ^ ") i) /\\
                   (!j. j < 1024 ==> read (memory :> bytes8 (word_add fp (word (12288 + j)))) s =
                                    " ^ string_of_term SI87_W1 ^ " j) /\\
                   read (memory :> bytes (word_add fp (word 14368),64)) s = C /\\
                   (!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (3072 + 4 * i)))) s =
                                    mld_sign_cphat 60 64 (" ^ string_of_term SI87_CT ^ ") i) /\\
                   (exists e2.
                      read events s = APPEND e2 e /\\
                      e2 = f_events fp rho C guard mf mc pc /\\
                      memaccess_inbounds e2 " ^ SI87_YCOL_READS ^ "))
              (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [X18; X19; X20; X21; X22; X23; X24; X30] ,,
               MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
               MAYCHANGE [memory :> bytes(word_sub fp (word 1472),1472);
                          memory :> bytes(word_add fp (word 100),4);
                          memory :> bytes(word_add fp (word 400),240);
                          memory :> bytes(word_add fp (word 624),4);
                          memory :> bytes(word_add fp (word 736),1024);
                          memory :> bytes(word_add fp (word 3072),1024);
                          memory :> bytes(word_add fp (word 4096),8192);
                          memory :> bytes(word_add fp (word 12288),1024);
                          memory :> bytes(word_add fp (word 13312),1024);
                          memory :> bytes(word_add fp (word 14336),96);
                          memory :> bytes(word_add fp (word 14448),984)])");;

let SI87_HEAD_EXEC = SI87_EXEC_RANGE "loop2" "after_mldsa_poly_ntt_2";;

let SI87_HEAD_ALLOWED = [`fp:int64`; `rho:num`; `C:num`; `guard:int64`; `mf:int64`;
                         `mc:int64`; `pc:num`];;

let SI87_HEAD_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc SI87_HEAD_EXEC name
    ilist SI87_HEAD_ALLOWED n;;

let SI87_ZX32 = prove
 (`!n. word_zx (word n:int64):int32 = word n`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

let SI87_SHL3 = prove
 (`!n. word_shl (word n:int32) 3 = word(8 * n)`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SHL; VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC MOD_DOWN_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let SI87_SUB87 = WORD_RULE `word_sub (word (8 * n)) (word n):int32 = word (7 * n)`;;

let SI87_ZX_32_16 = prove
 (`!n. word_zx (word n:int32):int16 = word n`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
  CONV_TAC(DEPTH_CONV NUM_MIN_CONV) THEN REWRITE_TAC[]);;

(*** kappa = 7 att = (att << 3) - att as str and strh store it ***)

let SI87_KAPPA_TAC =
  SI87_ASM_RW_TAC[SI87_ZX32; WORD_ZX_ZX_32_64_32] THEN
  SI87_ASM_RW_TAC[SI87_SHL3; WORD_ZX_ZX_32_64_32] THEN
  SI87_ASM_RW_TAC[SI87_SUB87; WORD_ZX_ZX_32_64_32] THEN
  SI87_ASM_RW_TAC[SI87_ZX_32_16];;

let SI87_HEAD_NUM_TAC =
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if can (find_term (fun t -> is_const t && fst(dest_const t) = "ensures")) c then th
    else if can (term_match [] `read PC s = x`) c || can (term_match [] `read X19 s = x`) c ||
       (is_forall c &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mld_lazy_acc")) c)
    then CONV_RULE(NUM_REDUCE_CONV THENC REWRITE_CONV[]) th else th);;

let SI87_HEAD_COL_TAC n k =
  SI87_REG_FORM_TAC "X19" (k - 1) (subst [mk_small_numeral n,`n:num`] `word (n + 1):int64`) THEN
  SI87_HEAD_CALL_TAC "H_YCJ" [`fp:int64`; `rho:num`; `RHO:num`; `att:num`; mk_small_numeral n;
                              `guard:int64`; `pc:num`] k THEN
  SI87_HEAD_NUM_TAC;;

let SI87_HEAD = prove
 (SI87_HEAD_STMT,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    MAP_EVERY (fun (th,n) -> SI87_ASSUME_CALLEE_TAILED_TAC th n)
     [MP (SPEC_ALL SI87_YCOL0) th,"H_YC0"; MP (SPEC_ALL SI87_YCOLJ) th,"H_YCJ";
      MATCH_MP (SPEC_ALL SI87_HPOST) (CONJUNCT1 th),"H_HP"]) THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(fp:int64) (rho:num) (C:num) (guard:int64) (mf:int64) (mc:int64) (pc:num).
      f_ev_head fp rho C guard mf mc pc:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `fp:int64`; `att:num`; `rho:num`; `RHO:num`;
                       `MU:num`; `C:num`; `guard:int64`; `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; fst SI87_HEAD_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SI87_ALIGNED16_32) THEN
  FULL_INIT_TAC THEN
  MAP_EVERY (fun n ->
    MP_TAC(SPECL [`word_add fp (word 1760):int64`; `32`; `rho:num`; mk_small_numeral n;
                  `s0:armstate`] SIGN_BYTES128_OF_BYTES) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC) [0;1] THEN
  ARM_STEPS_TAC SI87_HEAD_EXEC (1--12) THEN
  SI87_KAPPA_TAC THEN SI87_ASM_RW_TAC[SI87_ZX32] THEN
  SUBGOAL_THEN `rho < 2 EXP (8 * 32)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if can (term_match []
       `read (memory :> bytes (word_add fp (word 1760),32)) s0 = rho`) (concl th)
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[READ_BYTES_BOUND; READ_COMPONENT_COMPOSE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`word_add fp (word 14368):int64`; `rho:num`; `2`; `s12:armstate`]
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
  SI87_HEAD_CALL_TAC "H_YC0" [`fp:int64`; `rho:num`; `RHO:num`; `att:num`; `guard:int64`;
                              `pc:num`] 13 THEN
  MAP_EVERY (fun n -> SI87_HEAD_COL_TAC n (14 + n)) (0--5) THEN
  SI87_HEAD_CALL_TAC "H_HP" [`fp:int64`; `rho:num`; `RHO:num`; `MU:num`; `att:num`; `C:num`;
                             `guard:int64`; `pc:num`] 20 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SI87_END_TAC);;

(* ------------------------------------------------------------------------- *)
(* s1 in the NTT domain and y, as in the 44 stages (ML-DSA-87: s1 at        *)
(* sk + 128, 7 polynomials of 96 bytes), with y sampled from rho'' (RHO, at  *)
(* fp + 1984) with the nonce 7 att + i.                                      *)
(* ------------------------------------------------------------------------- *)

let SI87_S1U =
 `mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte)(128 + j))`;;
let SI87_S1H = mk_comb(`mld_polyvec_map mld_poly_ntt`,SI87_S1U);;
let SI87_YK = `mld_sign_y mld_poly_uniform_gamma1_19 RHO (7 * att)`;;
let SI87_ZI = list_mk_comb(`mld_sign_z`, [SI87_S1H; `cphat:num->int32`; SI87_YK; `i:num`]);;

(* ------------------------------------------------------------------------- *)
(* One iteration of the loop over z (ZIT), from loop43 with i in x20, 96 i  *)
(* in x19 and the pointer sig + 640 i in x25: s1_i unpacked into fp + 2048   *)
(* (x23) and transformed, its product with the challenge (fp + 3072) and    *)
(* the inverse NTT, y_i sampled again (the inlined poly_uniform_gamma1 with *)
(* the nonce 7 att + i, i saved at fp + 624 around it), the sum, the        *)
(* reduction and the norm check of z_i; if it passes (ok), z_i packed into  *)
(* the signature at sig + 64 + 640 i and back to loop43 or, after the last, *)
(* to loop43_exit1; else to join10. The pointer of rho'' is kept in x22     *)
(* across the packing (x25 holds the output pointer there).                 *)
(* ------------------------------------------------------------------------- *)

let SI87_ZIT_COMMON =
 "read SP s = fp /\\
  read X21 s = word_add fp (word 14336) /\\ read X27 s = word_add fp (word 13312) /\\
  read X28 s = word 18446744073701171199 /\\ read X26 s = word 252236767799803904 /\\
  read (memory :> bytes64 (word_add fp (word 176))) s = word_add fp (word 3072) /\\
  read (memory :> bytes64 (word_add fp (word 184))) s = word_add fp (word 1984) /\\
  read (memory :> bytes64 (word_add fp (word 704))) s = word_add sk (word 128) /\\
  read (memory :> bytes64 (word_add fp (word 216))) s = word_add fp (word 14761) /\\
  read (memory :> bytes64 (word_add fp (word 14336))) s = word_add fp (word 1984) /\\
  read (memory :> bytes16 (word_add fp (word 14344))) s = word (7 * att) /\\
  read (memory :> bytes128 (word_add fp (word 192))) s =
  word 339618401959998730991157055895298383871 /\\
  read (memory :> bytes (word_add fp (word 1984),64)) s = RHO /\\
  (!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (3072 + 4 * i)))) s =
                   cphat i) /\\
  (!i. i < 4896 ==> read (memory :> bytes8 (word_add sk (word i))) s = skb i) /\\
  read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
  read (memory :> bytes(ea,el)) s = ev";;

let SI87_ZIT_PRE =
  "read X23 s = word_add fp (word 2048) /\\ read X0 s = word 2 /\\\n" ^ SI87_ZIT_COMMON;;

let SI87_ZIT_READS =
 "[sig,4627; sk,4896; word_sub fp (word 1472),16928;
   word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
   word(pc + rodata_mld_KeccakF_RoundConstants),192;
   word(pc + rodata_mld_zetas),1024;
   word(pc + mldsa87_signature_internal_consts),400]
  [sig,4627; word_sub fp (word 1472),16928]";;

let SI87_ZIT_NOV =
 "nonoverlapping (sig,4627) (word_sub fp (word 1472),16928) /\\
  ALL (nonoverlapping (word_sub fp (word 1472),16928))
      [(sk,4896); (word pc,libmldsa_size); (word(pc + got_memset),8);
       (word(pc + got_memcpy),8); (ea,el)] /\\
  ALL (nonoverlapping (sig,4627))
      [(sk,4896); (word pc,libmldsa_size); (word(pc + got_memset),8);
       (word(pc + got_memcpy),8); (ea,el)]";;

let SI87_ZIT_STMT = parse_term(
 "!mf mc ea el ev.
   memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
   ==> exists f_events.
        forall e ok sig sk skb fp i cphat RHO att pc.
         aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
         aligned 32 fp /\\ i < 7 /\\ att < 9361 /\\
         (ok <=> mld_poly_chknorm (" ^ string_of_term SI87_ZI ^ ") (word 524168) = word 0) /\\
         " ^ SI87_ZIT_NOV ^ "
         ==> ensures arm
              (\\s. aligned_bytes_loaded s (word pc)
                     mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                   read PC s = word (pc + mldsa87_signature_internal_loop43) /\\
                   read X20 s = word i /\\ read X19 s = word (96 * i) /\\
                   read X25 s = word_add sig (word (640 * i)) /\\\n" ^ SI87_ZIT_PRE ^ " /\\
                   read events s = e)
              (\\s. read PC s =
                   (if ok then (if i + 1 < 7 then word (pc + mldsa87_signature_internal_loop43)
                                else word (pc + mldsa87_signature_internal_loop43_exit1))
                    else word (pc + mldsa87_signature_internal_join10)) /\\
                   read SP s = fp /\\
                   read X21 s = word_add fp (word 14336) /\\
                   (ok ==> read X20 s = word (i + 1) /\\ read X19 s = word (96 * (i + 1)) /\\
                           read X25 s = word_add sig (word (640 * (i + 1))) /\\
                           read X22 s = word_add fp (word 1984) /\\
                           read X23 s = word_add fp (word 2048) /\\ read X0 s = word 2 /\\
                           (!t. t < 640
                                ==> read (memory :> bytes8 (word_add sig (word ((64 + 640 * i) + t)))) s =
                                    mld_polyz_pack_19 (" ^ string_of_term SI87_ZI ^ ") t)) /\\
                   (~ok ==> read X25 s = word_add fp (word 1984) /\\
                            read X22 s = word_add fp (word 14448)) /\\
                   (exists e2.
                      read events s = APPEND e2 e /\\
                      e2 = f_events ok sig sk fp i mf mc pc /\\
                      memaccess_inbounds e2 " ^ SI87_ZIT_READS ^ "))
              (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [X18; X19; X20; X21; X22; X23; X24; X25; X30] ,,
               MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
               MAYCHANGE [memory :> bytes(word_sub fp (word 240),240);
                          memory :> bytes(word_add fp (word 208),8);
                          memory :> bytes(word_add fp (word 224),416);
                          memory :> bytes(word_add fp (word 2048),1024);
                          memory :> bytes(word_add fp (word 13312),1024);
                          memory :> bytes(word_add fp (word 14448),984);
                          memory :> bytes(word_add sig (word (64 + 640 * i)),640)])");;

let SI87_ZIT_EXEC = SI87_EXEC_RANGE "loop43" "loop43_exit1";;

let SI87_ZIT_TEMPLATE =
 `\(ok:bool) (sig:int64) (sk:int64) (fp:int64) (i:num) (mf:int64) (mc:int64) (pc:num).
   if ok then (if i + 1 < 7 then f_ev_mid sig sk fp i mf mc pc
               else f_ev_last sig sk fp i mf mc pc)
   else f_ev_f sig sk fp i mf mc pc :(uarch_event)list`;;

let SI87_ZIT_ALLOWED = [`ok:bool`; `sig:int64`; `sk:int64`; `fp:int64`; `i:num`;
                        `mf:int64`; `mc:int64`; `pc:num`];;

let SI87_ZIT_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc SI87_ZIT_EXEC
    name ilist SI87_ZIT_ALLOWED n;;

(*** Bytes 128 + 96 i .. of the key at state st (i < 7) ***)

let SI87_S1_SLICE_TAC st =
  let t = vsubst [st,`s:armstate`]
   `!k. k < 96 ==> read (memory :> bytes8 (word_add sk (word (128 + 96 * i + k)))) s =
                   (skb:num->byte) (128 + 96 * i + k)` in
  SUBGOAL_THEN t ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (term_match []
       `!i. i < 4896 ==> read (memory :> bytes8 (word_add sk (word i))) s = skb i`)
       (concl th))) THEN
    MAP_EVERY UNDISCH_TAC [`i < 7`; `k < 96`] THEN ARITH_TAC;
    ALL_TAC];;

(*** The 16-bit nonce as ldrh loads it ***)

let SI87_ZX16 = prove
 (`!n. n < 65536 ==> word_zx (word_zx (word n:int16):int32):int64 = word n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_16; DIMINDEX_32;
              DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `n MOD 65536 = n /\ n MOD 4294967296 = n /\
                n MOD 18446744073709551616 = n` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_REWRITE_TAC[]]);;

let SI87_ZTEST7 = prove
 (`!i. i < 7
       ==> (val (word_add (word i) (word 18446744073709551610):int64) = 0 <=>
            ~(i + 1 < 7))`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let SI87_ZIT_POLY v = mk_comb(mk_comb(`mld_poly_of`,v),`i:num`);;
let SI87_ZIT_PW = list_mk_comb(`mld_poly_pointwise_montgomery`,
  [SI87_ZIT_POLY SI87_S1H; `cphat:num->int32`]);;
let SI87_ZIT_CS1 = mk_comb(`mld_poly_invntt_tomont`,SI87_ZIT_PW);;
let SI87_ZIT_Y = SI87_ZIT_POLY SI87_YK;;

let SI87_STEPS_ADRP_TAC exec adrps ns =
  MAP_EVERY (fun n -> ARM_STEPS_TAC exec [n] THEN
                      (if mem n adrps then MLKEM_NATIVE_ADRP_TAC else ALL_TAC)) ns;;

let SI87_ZIT_CALLEES th =
  ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP SI87_G1_Z th) "H_G1" THEN
  MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
   [SI87_ETA_ZTH,"H_ETA";
    MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_NTT";
    MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_INV";
    SI87_LK SI87_PWM "loop46","H_PWM46"; SI87_ZADD,"H_ZADD";
    SI87_LK SI87_RED "loop49","H_RED49"; SI87_LK SI87_CHK "loop50","H_CHK50";
    SI87_ZPACK,"H_ZPACK"];;

(*** From loop43 to the norm check of z_i (step 57) ***)

let SI87_ZIT_PART1_TAC =
  SI87_S1_SLICE_TAC `s0:armstate` THEN
  SI87_ZIT_CALL_TAC "H_ETA" [`fp:int64`; `word_add sk (word 128):int64`; `i:num`;
    `\k. (skb:num->byte) (128 + 96 * i + k)`; `word_add sig (word (640 * i)):int64`;
    `pc:num`] 1 THEN
  MLD_LAZY_REPOLY_TAC `mld_polyeta_unpack_2 (\k. (skb:num->byte) (128 + 96 * i + k))`
    (SI87_ZIT_POLY SI87_S1U) [mld_polyvec_unpack; MLD_POLY_OF_POLYVEC] THEN
  ARM_STEPS_TAC SI87_ZIT_EXEC (2--3) THEN
  SI87_ZIT_CALL_TAC "H_NTT" [`read X0 s`; SI87_ZIT_POLY SI87_S1U; `pc:num`;
                              `read SP s`; `read X30 s`] 4 THEN
  MLD_LAZY_REPOLY_TAC (mk_comb(`mld_poly_ntt`,SI87_ZIT_POLY SI87_S1U))
    (SI87_ZIT_POLY SI87_S1H) [MLD_POLY_OF_POLYVEC_MAP] THEN
  ARM_STEPS_TAC SI87_ZIT_EXEC (5--6) THEN
  SI87_ZIT_CALL_TAC "H_PWM46" [`word_add fp (word 2048):int64`;
    `word_add fp (word 3072):int64`; SI87_ZIT_POLY SI87_S1H; `cphat:num->int32`;
    `pc:num`] 7 THEN
  ARM_STEPS_TAC SI87_ZIT_EXEC (8--9) THEN
  SI87_ZIT_CALL_TAC "H_INV" [`read X0 s`; SI87_ZIT_PW; `pc:num`; `read SP s`;
                              `read X30 s`] 10 THEN
  (*** y_i ***)
  ARM_STEPS_TAC SI87_ZIT_EXEC (11--16) THEN
  SUBGOAL_THEN `7 * att < 65536` ASSUME_TAC THENL
   [UNDISCH_TAC `att < 9361` THEN ARITH_TAC; ALL_TAC] THEN
  SI87_ASM_RW_TAC[MP (SPEC `7 * att` SI87_ZX16) (ASSUME `7 * att < 65536`)] THEN
  MAP_EVERY ASSUME_TAC SI87_FR_EQS THEN
  SI87_ZIT_CALL_TAC "H_G1" [`word_add fp (word 1984):int64`; `RHO:num`; `7 * att`;
    `i:num`; `word_sub fp (word 240):int64`; `pc:num`] 17 THEN
  SI87_ASM_RW_TAC SI87_FR_EQS THEN
  MLD_LAZY_REPOLY_TAC `mld_poly_uniform_gamma1_19 RHO (word (7 * att + i))` SI87_ZIT_Y
    [mld_sign_y; MLD_POLY_OF_POLYVEC] THEN
  (*** z_i = c s1_i + y_i, reduced, and its check ***)
  SI87_STEPS_ADRP_TAC SI87_ZIT_EXEC [31;33;34;36;37;39;40;41] (18--41) THEN
  SI87_ZIT_CALL_TAC "H_ZADD" [`fp:int64`; SI87_ZIT_CS1; SI87_ZIT_Y;
    `word_add fp (word 1984):int64`; `pc:num`] 42 THEN
  SI87_ZIT_CALL_TAC "H_RED49" [`word_add fp (word 2048):int64`;
    list_mk_comb(`mld_poly_add`,[SI87_ZIT_CS1; SI87_ZIT_Y]); `pc:num`] 43 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_z]) THEN
  SI87_STEPS_ADRP_TAC SI87_ZIT_EXEC (49--54) (44--54) THEN
  SI87_REG_FORM_TAC "X13" 54
    `word_zx (word_sub (word_sub (word 524168:int32) (word 1)) (word 390)):int64` THEN
  SI87_REG_FORM_TAC "X8" 54 `word_zx (word 0:int32):int64` THEN
  SI87_ZIT_CALL_TAC "H_CHK50" [`word_add fp (word 2048):int64`; SI87_ZI;
    `word 524168:int32`; `word 0:int32`; `pc:num`] 55 THEN
  ARM_STEPS_TAC SI87_ZIT_EXEC (56--57) THEN
  SI87_DECIDE_TAC `ok:bool` THEN SI87_CASES_TAC `ok:bool`;;

(*** The packing of z_i and the back edge ***)

let SI87_ZIT_BYTES_TAC =
  X_GEN_TAC `t:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(64 + 640 * i) + t = 640 * i + 64 + t` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;;

let SI87_ZIT_PART2_TAC =
  SI87_STEPS_ADRP_TAC SI87_ZIT_EXEC [62;63;64] (58--64) THEN
  SI87_ZIT_CALL_TAC "H_ZPACK" [`fp:int64`; `word_add sig (word (640 * i)):int64`;
    SI87_ZI; `pc:num`] 65 THEN
  ARM_STEPS_TAC SI87_ZIT_EXEC (66--75) THEN
  SI87_ASM_RW_TAC[MP (SPEC `i:num` SI87_ZTEST7) (ASSUME `i < 7`)] THEN
  SI87_CASES_TAC `i + 1 < 7` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES; ADD_ASSOC] THEN
      CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(SI87_ZIT_BYTES_TAC THEN NO_TAC) THEN
  SI87_END_TAC;;

let SI87_ZIT_SETUP_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN SI87_ZIT_CALLEES THEN
  CONCRETIZE_F_EVENTS_TAC SI87_ZIT_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `ok:bool`; `sig:int64`; `sk:int64`;
    `skb:num->byte`; `fp:int64`; `i:num`; `cphat:num->int32`; `RHO:num`; `att:num`;
    `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; fst SI87_ZIT_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SI87_ALIGNED16_32) THEN
  FIRST_X_ASSUM(fun th -> if is_iff(concl th) && lhs(concl th) = `ok:bool`
                          then ASSUME_TAC(GSYM th) else NO_TAC) THEN
  FULL_INIT_TAC;;

let SI87_ZIT = prove
 (SI87_ZIT_STMT,
  SI87_ZIT_SETUP_TAC THEN SI87_ZIT_PART1_TAC THENL
   [SI87_ZIT_PART2_TAC; SI87_RIT_FAIL_TAC `ok:bool`]);;

(* ------------------------------------------------------------------------- *)
(* The loop over z, for the first m polynomials, each of which passes the    *)
(* norm check (ZPRE), from after the NTT of the challenge, where the code    *)
(* sets up i = 0 (x25 = sig from [fp + 88], x23 = fp + 2048, w0 = 2), as in *)
(* the 44 stages: the first 640 m bytes of z packed are at sig + 64.         *)
(* ------------------------------------------------------------------------- *)

let SI87_ZPRE_Z = list_mk_comb(`mld_sign_z`, [SI87_S1H; `cphat:num->int32`; SI87_YK]);;
let SI87_ZPRE_ZI = mk_comb(SI87_ZPRE_Z,`i:num`);;

let SI87_ZPRE_STMT = parse_term(
 "!mf mc ea el ev.
   memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
   ==> exists f_events.
        forall e m sig sk skb fp cphat RHO att pc.
         aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
         aligned 32 fp /\\ m <= 7 /\\ att < 9361 /\\
         (!i. i < m ==> mld_poly_chknorm (" ^ string_of_term SI87_ZPRE_ZI ^ ") (word 524168) =
                        word 0) /\\
         " ^ SI87_ZIT_NOV ^ "
         ==> ensures arm
              (\\s. aligned_bytes_loaded s (word pc)
                     mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                   read PC s = word (pc + mldsa87_signature_internal_after_mldsa_poly_ntt_2) /\\
                   read (memory :> bytes64 (word_add fp (word 88))) s = sig /\\\n" ^
  SI87_ZIT_COMMON ^ " /\\
                   read events s = e)
              (\\s. read PC s =
                   (if m < 7 then word (pc + mldsa87_signature_internal_loop43)
                    else word (pc + mldsa87_signature_internal_loop43_exit1)) /\\
                   read SP s = fp /\\
                   read X20 s = word m /\\ read X19 s = word (96 * m) /\\
                   read X25 s = word_add sig (word (640 * m)) /\\
                   read X23 s = word_add fp (word 2048) /\\ read X0 s = word 2 /\\
                   read X21 s = word_add fp (word 14336) /\\
                   (0 < m ==> read X22 s = word_add fp (word 1984)) /\\
                   (!t. t < 640 * m
                        ==> read (memory :> bytes8 (word_add sig (word (64 + t)))) s =
                            mld_polyvec_pack 640 mld_polyz_pack_19
                             (mld_polyvec (" ^ string_of_term SI87_ZPRE_Z ^ ")) t) /\\
                   (exists e2.
                      read events s = APPEND e2 e /\\
                      e2 = f_events m sig sk fp mf mc pc /\\
                      memaccess_inbounds e2 " ^ SI87_ZIT_READS ^ "))
              (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [X18; X19; X20; X21; X22; X23; X24; X25; X30] ,,
               MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
               MAYCHANGE [memory :> bytes(word_sub fp (word 240),240);
                          memory :> bytes(word_add fp (word 208),8);
                          memory :> bytes(word_add fp (word 224),416);
                          memory :> bytes(word_add fp (word 2048),1024);
                          memory :> bytes(word_add fp (word 13312),1024);
                          memory :> bytes(word_add fp (word 14448),984);
                          memory :> bytes(word_add sig (word 64),4480)])");;

let SI87_ZPRE_EXEC = SI87_EXEC_RANGE "after_mldsa_poly_ntt_2" "loop43_exit1";;

let SI87_ZPRE_INV = parse_term(
 "\\i s. read X20 s = word i /\\ read X19 s = word (96 * i) /\\
        read X25 s = word_add sig (word (640 * i)) /\\
        read X23 s = word_add fp (word 2048) /\\ read X0 s = word 2 /\\
        (0 < i ==> read X22 s = word_add fp (word 1984)) /\\
        read (memory :> bytes64 (word_add fp (word 88))) s = sig /\\\n" ^ SI87_ZIT_COMMON ^ " /\\
        (!t. t < 640 * i
             ==> read (memory :> bytes8 (word_add sig (word (64 + t)))) s =
                 mld_polyvec_pack 640 mld_polyz_pack_19
                  (mld_polyvec (" ^ string_of_term SI87_ZPRE_Z ^ ")) t)");;

let SI87_ZPRE_ALLOWED = [`sig:int64`; `sk:int64`; `fp:int64`; `mf:int64`; `mc:int64`;
                         `pc:num`; `i:num`];;

let SI87_ZPRE_PC = prove
 (`!i m a b. i < m /\ m <= 7
             ==> (if i + 1 < 7 then word a else word b):int64 =
                 word (if i + 1 < m then a else if m < 7 then a else b)`,
  REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMPLE_ARITH_TAC);;

let SI87_ZPRE_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `i < 7` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o C MP (ASSUME `i < m`) o SPEC `i:num` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `mld_poly_chknorm`)) (concl th))) THEN
  FULL_INIT_TAC THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc SI87_ZPRE_EXEC "H_ZIT"
   [`T`; `sig:int64`; `sk:int64`; `skb:num->byte`; `fp:int64`; `i:num`;
    `cphat:num->int32`; `RHO:num`; `att:num`; `pc:num`] SI87_ZPRE_ALLOWED 1 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SI87_ZPRE_PC
                               (CONJ (ASSUME `i < m`) (ASSUME `m <= 7`))]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC(ISPECL [`mld_polyz_pack_19`; `640`] SIGN_PACK_JOIN) THEN
      ASM_REWRITE_TAC[SIGN_POLYZ_PACK_19_LOCAL] THEN
      REWRITE_TAC[ADD_ASSOC] THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
  (SI87_MAYCHANGE_TAC ORELSE SI87_LOOP_END_TAC);;

let SI87_ZPRE_SETUP_TAC = ARM_STEPS_TAC SI87_ZPRE_EXEC (1--5);;

let SI87_ZPRE = prove
 (SI87_ZPRE_STMT,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    SI87_ASSUME_CALLEE_TAILED_TAC (MATCH_MP SI87_ZIT th) "H_ZIT") THEN
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
              fst SI87_ZPRE_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SI87_ALIGNED16_32) THEN
  ASM_CASES_TAC `0 < m` THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `m:num`
     `pc + mldsa87_signature_internal_loop43`
     `if m < 7 then pc + mldsa87_signature_internal_loop43
      else pc + mldsa87_signature_internal_loop43_exit1`
     SI87_ZPRE_INV THEN
    REPEAT CONJ_TAC THENL
     [SIMPLE_ARITH_TAC;
      REWRITE_TAC[CONJUNCT1 LT; MULT_CLAUSES; ADD_CLAUSES; LE_0] THEN
      FULL_INIT_TAC THEN SI87_ZPRE_SETUP_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN SI87_END_TAC;
      SI87_ZPRE_BODY_TAC;
      REWRITE_TAC[] THEN FULL_INIT_TAC THEN SIGN_PC_COND_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      SIGN_BETA_ALL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC];
    SUBGOAL_THEN `m = 0` SUBST_ALL_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN SI87_ZPRE_SETUP_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ARITH; MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    REWRITE_TAC[ENUMERATEL; APPEND; APPEND_NIL] THEN SI87_CLOSED_END_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The packing of c~ and of the hints (TAIL), from the exit of the loop over *)
(* the rows (loop52_exit1): c~ (64 bytes at fp + 14368) copied to sig, the   *)
(* hints zeroed, and for each row k the unpacking of its w1 (SI87_W1U0 /     *)
(* SI87_W1UK) and its hints (SI87_HROW), with the count of row k stored at  *)
(* sig + 4619 + k (by the unpacking of the next row, and after row 7). Row  *)
(* 0 lies before the cleanup (join12) in the code, rows 1 to 7 after it. If *)
(* the hints fit, the code sets w19 to 1 and goes to the cleanup at join12  *)
(* with the hints of mld_pack_hints at sig + 4544; otherwise it goes there  *)
(* through join10 with w19 = 0.                                              *)
(* ------------------------------------------------------------------------- *)

let SI87_TAIL_STMT = parse_term(
 "exists f_events.
    forall e sig fp (C:num) (x:num->int32) (b:num->byte) pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 16 fp /\\
      nonoverlapping (sig,4627) (word_sub fp (word 1472),16928) /\\
      ALL (nonoverlapping (word pc,libmldsa_size))
          [(sig,4627); (word_sub fp (word 1472),16928)]
      ==> ensures arm
           (\\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read PC s = word (pc + mldsa87_signature_internal_loop52_exit1) /\\
                read SP s = fp /\\
                read X27 s = word_add fp (word 13312) /\\
                read X14 s = word 523777 /\\
                read (memory :> bytes64 (word_add fp (word 88))) s = sig /\\
                read (memory :> bytes64 (word_add fp (word 32))) s =
                word_add sig (word 4544) /\\
                read (memory :> bytes64 (word_add fp (word 72))) s =
                word_add sig (word 4096) /\\\n" ^
  SI87_SLOT_FACTS [40,8192; 48,7168; 56,6144; 64,5120; 144,11264; 152,10240; 160,9216] ^
 "              read (memory :> bytes (word_add fp (word 14368),64)) s = C /\\
                (!j. j < 2048 ==> read (memory :> bytes32 (word_add fp (word (4096 + 4 * j)))) s = x j) /\\
                (!j. j < 1024 ==> read (memory :> bytes8 (word_add fp (word (12288 + j)))) s = b j) /\\
                read events s = e)
           (\\s. read PC s = word (pc + mldsa87_signature_internal_join12) /\\
                read SP s = fp /\\
                read X19 s =
                (if mld_hint_count (mld_polyvec_make_hint_32 x b) 2048 <= 75
                 then word 1 else word 0) /\\
                read (memory :> bytes (sig,64)) s = C /\\
                (mld_hint_count (mld_polyvec_make_hint_32 x b) 2048 <= 75
                 ==> !t. t < 83
                         ==> read (memory :> bytes8 (word_add sig (word (4544 + t)))) s =
                             mld_pack_hints 75 8 (mld_polyvec_make_hint_32 x b) t) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events sig fp pc x b /\\
                   memaccess_inbounds e2
                    [sig,4627; word_sub fp (word 1472),16928]
                    [sig,4627; word_sub fp (word 1472),16928]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
            MAYCHANGE [X19; X23] ,,
            MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
            MAYCHANGE [memory :> bytes(sig,64);
                       memory :> bytes(word_add sig (word 4544),83);
                       memory :> bytes(word_add fp (word 13312),1024)])");;

let SI87_TAIL_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [(layout "mldsa87_signature_internal_loop52_exit1",
     layout "mldsa87_signature_internal_loop63");
    (layout "mldsa87_signature_internal_loop62_exit2",
     layout "mldsa87_signature_internal_loop2_exit2")];;

let SI87_TL_CNT_TM p = subst [mk_small_numeral p,`p:num`]
  `mld_hint_count (mld_polyvec_make_hint_32 x b) p <= 75`;;

let SI87_TL_TEMPLATE =
  let rec mk k =
    if k = 8 then `f_ev_ok (sig:int64) (fp:int64) (pc:num) (x:num->int32) (b:num->byte):(uarch_event)list`
    else mk_cond(SI87_TL_CNT_TM (256 * (k + 1)), mk (k + 1),
                 list_mk_comb(mk_var("f_ev_r" ^ string_of_int k,
                   `:int64->int64->num->(num->int32)->(num->byte)->(uarch_event)list`),
                   [`sig:int64`; `fp:int64`; `pc:num`; `x:num->int32`; `b:num->byte`])) in
  list_mk_abs([`sig:int64`; `fp:int64`; `pc:num`; `x:num->int32`; `b:num->byte`], mk 0);;

let SI87_TL_ALLOWED = [`sig:int64`; `fp:int64`; `pc:num`; `x:num->int32`; `b:num->byte`];;

let SI87_TL_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc SI87_TAIL_EXEC
    name ilist SI87_TL_ALLOWED n;;

(*** The facts for row k of b and of x at state n ***)

let SI87_TL_B_SLICE_TAC k n =
  let ib = 12288 + 128 * k and wb = 128 * k in
  let st = mk_var("s"^string_of_int n,`:armstate`) in
  SUBGOAL_THEN (vsubst [st,`s:armstate`] (parse_term(Printf.sprintf
    "!j. j < 128 ==> read (memory :> bytes8 (word_add fp (word (%d + j)))) s = b (%d + j)" ib wb)))
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC (parse_term(Printf.sprintf "%d + j" wb)) o check (fun th ->
      is_forall(concl th) && can (term_match []
       `!j. j < 1024 ==> read (memory :> bytes8 (word_add fp (word (12288 + j)))) s = b j`)
       (concl th))) THEN
    REWRITE_TAC[ARITH_RULE(parse_term(Printf.sprintf "12288 + %d + j = %d + j" wb ib))] THEN
    DISCH_THEN MATCH_MP_TAC THEN UNDISCH_TAC `j < 128` THEN ARITH_TAC;
    ALL_TAC];;

let SI87_TL_X_SLICE_TAC k n =
  let w = 4096 + 1024 * k and p0 = 256 * k in
  let st = mk_var("s"^string_of_int n,`:armstate`) in
  SUBGOAL_THEN (vsubst [st,`s:armstate`] (parse_term(Printf.sprintf
    "!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (%d + 4 * i)))) s = x (%d + i)" w p0)))
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC (parse_term(Printf.sprintf "%d + i" p0)) o check (fun th ->
      is_forall(concl th) && can (term_match []
       `!j. j < 2048 ==> read (memory :> bytes32 (word_add fp (word (4096 + 4 * j)))) s = x j`)
       (concl th))) THEN
    REWRITE_TAC[ARITH_RULE(parse_term(Printf.sprintf "4096 + 4 * (%d + i) = %d + 4 * i" p0 w))] THEN
    DISCH_THEN MATCH_MP_TAC THEN UNDISCH_TAC `i < 256` THEN ARITH_TAC;
    ALL_TAC];;

let SI87_TL_SPLIT_TAC p =
  let c = SI87_TL_CNT_TM p in
  ASM_CASES_TAC c THEN
  FIRST_ASSUM(fun th -> if concl th = c || concl th = mk_neg c
    then RULE_ASSUM_TAC(fun th' -> if concl th' = concl th then th' else REWRITE_RULE[th] th')
    else NO_TAC) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && free_in `X8` (concl th)
                                then STRIP_ASSUME_TAC th else NO_TAC));;

(*** Too many hints: through join10 (2 instructions from step n) ***)

let SI87_TL_FAIL_TAC p n =
  SUBGOAL_THEN (mk_neg(SI87_TL_CNT_TM 2048)) ASSUME_TAC THENL
   [MP_TAC(SPECL [`mld_polyvec_make_hint_32 x b`; mk_small_numeral p; `2048`]
                 MLD_HINT_COUNT_MONO) THEN
    FIRST_ASSUM(MP_TAC o check (fun th -> concl th = mk_neg(SI87_TL_CNT_TM p))) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ARM_STEPS_TAC SI87_TAIL_EXEC (n--(n+1)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SI87_SAFETY_TAC;;

let SI87_TL_PACK_TAC =
  X_GEN_TAC `t:num` THEN DISCH_TAC THEN REWRITE_TAC[mld_pack_hints] THEN
  CONV_TAC NUM_REDUCE_CONV THEN COND_CASES_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    SUBGOAL_THEN `t = 75 \/ t = 76 \/ t = 77 \/ t = 78 \/ t = 79 \/ t = 80 \/
                  t = 81 \/ t = 82` MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`t < 83`; `~(t < 75)`] THEN ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[SI87_ZX_BYTE]];;

(*** Row k > 0: the unpacking of w1 (step 2k + 1) and the hints (2k + 2) ***)

let SI87_TL_ROW_TAC k =
  let p1 = 256 * (k + 1) in
  let nw = 2 * k + 1 in let nh = nw + 1 in
  SI87_TL_B_SLICE_TAC k (nw - 1) THEN
  SI87_TL_CALL_TAC ("H_W1U"^string_of_int k)
   [`fp:int64`; parse_term(Printf.sprintf "\\t. (b:num->byte) (%d + t)" (128 * k));
    `sig:int64`; parse_term(Printf.sprintf
      "mld_hint_count (mld_polyvec_make_hint_32 x b) %d" (256 * k)); `pc:num`] nw THEN
  SI87_TL_X_SLICE_TAC k nw THEN
  SI87_TL_CALL_TAC ("H_HROW"^string_of_int k)
   [`x:num->int32`; `b:num->byte`; `sig:int64`; `fp:int64`; `pc:num`] nh THEN
  SI87_TL_SPLIT_TAC p1 THENL [ALL_TAC; SI87_TL_FAIL_TAC p1 (nh+1)];;

let SI87_TAIL_SETUP_TAC =
  MAP_EVERY (fun (th,n) -> SI87_ASSUME_CALLEE_TAILED_TAC th n)
   ((SI87_W1U0,"H_W1U0") ::
    zip SI87_W1UK (map (fun k -> "H_W1U" ^ string_of_int k) (1--7)) @
    zip SI87_HROW (map (fun k -> "H_HROW" ^ string_of_int k) (0--7))) THEN
  CONCRETIZE_F_EVENTS_TAC SI87_TL_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `sig:int64`; `fp:int64`; `C:num`;
                       `x:num->int32`; `b:num->byte`; `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; fst SI87_TAIL_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN
  MAP_EVERY (fun n ->
    MP_TAC(SPECL [`word_add fp (word 14368):int64`; `64`; `C:num`; mk_small_numeral n;
                  `s0:armstate`] SIGN_BYTES128_OF_BYTES) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC) [0;1;2;3];;

(*** Row 0: c~, the zeroing, the unpacking and the hints ***)

let SI87_TAIL_ROW0_TAC =
  SI87_TL_B_SLICE_TAC 0 0 THEN
  SI87_TL_CALL_TAC "H_W1U0"
   [`fp:int64`; `\t. (b:num->byte) (0 + t)`; `sig:int64`;
    `read (memory :> bytes128 (word_add fp (word 14368))) s`;
    `read (memory :> bytes128 (word_add fp (word 14384))) s`;
    `read (memory :> bytes128 (word_add fp (word 14400))) s`;
    `read (memory :> bytes128 (word_add fp (word 14416))) s`; `pc:num`] 1 THEN
  (*** sig[0,64) = C ***)
  SUBGOAL_THEN `C < 2 EXP (8 * 64)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if can (term_match []
       `read (memory :> bytes (word_add fp (word 14368),64)) s0 = C`) (concl th)
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[READ_BYTES_BOUND; READ_COMPONENT_COMPOSE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`sig:int64`; `C:num`; `4`; `s1:armstate`] SIGN_BYTES_OF_BYTES128) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0; DIV_1] THEN ASM_REWRITE_TAC[DIV_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `C MOD 2 EXP (128 * 4) = C` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN
    FIRST_ASSUM(MP_TAC o check (fun th -> concl th = `C < 2 EXP (8 * 64)`)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN DISCH_TAC THEN
  (*** the zero hints as mld_hint_index h 0, the count 0 ***)
  FIRST_X_ASSUM(fun th ->
    if can (term_match []
         `!t. t < 75 ==> read (memory :> bytes8 (word_add sig (word (4544 + t)))) s1 =
                         word 0`) (concl th)
    then ASSUME_TAC(GEN `t:num`
      (REWRITE_RULE[GSYM(INST [`mld_polyvec_make_hint_32 x b`,`h:num->bool`]
                               (CONJUNCT1 mld_hint_index))]
         (SPEC `t:num` th)))
    else NO_TAC) THEN
  SI87_TL_X_SLICE_TAC 0 1 THEN
  (let c0 = INST [`mld_polyvec_make_hint_32 x b`,`h:num->bool`]
                 (CONJUNCT1 mld_hint_count) in
   ASSUME_TAC c0 THEN ASSUME_TAC(REWRITE_RULE[GSYM c0] (ARITH_RULE `0 <= 75`)) THEN
   FIRST_X_ASSUM(fun th -> if concl th = `read X8 s1 = word 0` then
     ASSUME_TAC(TRANS th (AP_TERM `word:num->int64` (SYM c0))) else NO_TAC)) THEN
  SI87_TL_CALL_TAC "H_HROW0"
   [`x:num->int32`; `b:num->byte`; `sig:int64`; `fp:int64`; `pc:num`] 2 THEN
  SI87_TL_SPLIT_TAC 256 THENL [ALL_TAC; SI87_TL_FAIL_TAC 256 3];;

let SI87_TAIL_END_TAC =
  ARM_STEPS_TAC SI87_TAIL_EXEC (17--20) THEN ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [SI87_TL_PACK_TAC; SI87_SAFETY_TAC];;

let SI87_TAIL = prove
 (SI87_TAIL_STMT,
  SI87_TAIL_SETUP_TAC THEN SI87_TAIL_ROW0_TAC THEN
  MAP_EVERY SI87_TL_ROW_TAC (1--7) THEN SI87_TAIL_END_TAC);;

(* ------------------------------------------------------------------------- *)
(* A whole attempt (ATT), from loop2 with its number att in w9 to the exit   *)
(* of the cleanup: to loop2_exit2 on success (r = 24), else to loop2 with    *)
(* att + 1 in w9 or, after the last attempt, to loop2_exit1. By cases on the *)
(* result r of mld_sign_attempt_declass, as in the 44 stages: r < 7 (z_r     *)
(* fails: ZPRE, then ZIT and join10), 7 <= r < 23 (check r - 7 of the rows   *)
(* fails: ZPRE, RPRE, then RIT and join11), 23 (too many hints) and 24       *)
(* (success), both through TAIL; then CLEAN from join12. The registers that  *)
(* the next attempt needs (x21, x22, x25, q7) are restored on every path.   *)
(* ------------------------------------------------------------------------- *)

let SI87_ATT_CPH = `mld_poly_ntt (mld_poly_challenge 60 64 C)`;;
let SI87_ATT_W = SI87_W;;
let SI87_ATT_R0 = list_mk_comb(`mld_sign_r0`,
  [`mld_poly_decompose_lo_32`; SI87_ATT_W; SI87_S2H; SI87_ATT_CPH]);;
let SI87_ATT_CT0 = list_mk_comb(`mld_sign_ct0`,[SI87_T0H; SI87_ATT_CPH]);;
let SI87_SIGATT = list_mk_comb(
 `mld_sign_attempt_sig 8 7 64 60 mld_poly_uniform_gamma1_19 mld_polyz_pack_19
   640 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128
   mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 75`,
  [`mld_polyvec_matrix_expand 7 rho`; SI87_S1H; SI87_S2H; SI87_T0H; `MU:num`; `RHO:num`;
   `7 * att`]);;

let SI87_ATT_STMT = parse_term(
 "!mf mc ea el ev.
   memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
   ==> exists f_events.
        forall e sig sk skb fp rho MU RHO att C r x b guard pc.
         aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
         aligned 32 fp /\\ att < 9361 /\\ mld_matrix_terminates 8 7 rho /\\
         mld_sign_attempt_declass 8 7 64 60 mld_poly_uniform_gamma1_19
          524168 261768 261888 (mld_polyw1_pack_32 o mld_poly_decompose_hi_32)
          128 mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 75
          (mld_polyvec_matrix_expand 7 rho) (" ^ string_of_term SI87_S1H ^ ")
          (" ^ string_of_term SI87_S2H ^ ") (" ^ string_of_term SI87_T0H ^ ")
          MU RHO (7 * att) = (C,r,x,b) /\\
         mld_poly_challenge_terminates 60 64 C /\\
         nonoverlapping (sig,4627) (word_sub fp (word 1472),16928) /\\
         ALL (nonoverlapping (word_sub fp (word 1472),16928))
             [(sk,4896); (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
              (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\\
         ALL (nonoverlapping (sig,4627))
             [(sk,4896); (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
              (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
         ==> ensures arm
              (\\s. aligned_bytes_loaded s (word pc)
                     mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                   read PC s = word (pc + mldsa87_signature_internal_loop2) /\\
                   read X9 s = word att /\\\n" ^ SI87_HEAD_PRE ^ " /\\\n" ^
  SI87_SLOT_FACTS [40,8192; 48,7168; 56,6144; 64,5120; 104,3080; 176,3072; 184,1984] ^
 "                 read (memory :> bytes64 (word_add fp (word 88))) s = sig /\\
                   read (memory :> bytes64 (word_add fp (word 32))) s =
                   word_add sig (word 4544) /\\
                   read (memory :> bytes64 (word_add fp (word 72))) s =
                   word_add sig (word 4096) /\\
                   read (memory :> bytes64 (word_add fp (word 640))) s = word_add sk (word 800) /\\
                   read (memory :> bytes64 (word_add fp (word 672))) s = word_add sk (word 1568) /\\
                   read (memory :> bytes64 (word_add fp (word 704))) s = word_add sk (word 128) /\\
                   (!i. i < 4896 ==> read (memory :> bytes8 (word_add sk (word i))) s = skb i) /\\
                   read events s = e)
              (\\s. read PC s =
                   (if r = 24 then word (pc + mldsa87_signature_internal_loop2_exit2)
                    else if att + 1 < 9361 then word (pc + mldsa87_signature_internal_loop2)
                    else word (pc + mldsa87_signature_internal_loop2_exit1)) /\\
                   read SP s = fp /\\
                   read X21 s = word_add fp (word 14336) /\\
                   read X22 s = word_add fp (word 14448) /\\
                   read X25 s = word_add fp (word 1984) /\\
                   read Q7 s = word 0 /\\
                   (~(r = 24) ==> read X9 s = word (att + 1)) /\\
                   read (memory :> bytes64(word(pc + got_stack_chk_guard))) s = guard /\\
                   read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                   read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                   read (memory :> bytes(ea,el)) s = ev /\\
                   (r = 24
                    ==> !t. t < 4627
                            ==> read (memory :> bytes8 (word_add sig (word t))) s =
                                (" ^ string_of_term SI87_SIGATT ^ ") t) /\\
                   (exists e2.
                      read events s = APPEND e2 e /\\
                      e2 = f_events sig sk fp rho att C r x b guard mf mc pc /\\
                      memaccess_inbounds e2
                       [sig,4627; sk,4896; word_sub fp (word 1472),16928;
                        word(pc + got_stack_chk_guard),8; guard,8;
                        word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                        word(pc + rodata_mld_KeccakF_RoundConstants),192;
                        word(pc + rodata_mld_zetas),1024;
                        word(pc + mldsa87_signature_internal_consts),400]
                       [sig,4627; word_sub fp (word 1472),16928]))
              (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [X18; X19; X20; X21; X22; X23; X24; X25; X30] ,,
               MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
               MAYCHANGE [memory :> bytes(sig,4627);
                          memory :> bytes(word_sub fp (word 1472),1472);
                          memory :> bytes(word_add fp (word 100),4);
                          memory :> bytes(word_add fp (word 168),8);
                          memory :> bytes(word_add fp (word 208),8);
                          memory :> bytes(word_add fp (word 224),416);
                          memory :> bytes(word_add fp (word 736),1024);
                          memory :> bytes(word_add fp (word 2048),1024);
                          memory :> bytes(word_add fp (word 3072),1024);
                          memory :> bytes(word_add fp (word 4096),8192);
                          memory :> bytes(word_add fp (word 12288),1024);
                          memory :> bytes(word_add fp (word 13312),1024);
                          memory :> bytes(word_add fp (word 14336),96);
                          memory :> bytes(word_add fp (word 14448),984)])");;

let SI87_ATT_EXEC = MLDSA_NATIVE_SIGNATURE_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;

let SI87_ATT_ALLOWED =
  [`sig:int64`; `sk:int64`; `fp:int64`; `rho:num`; `att:num`; `C:num`; `r:num`;
   `x:num->int32`; `b:num->byte`; `guard:int64`; `mf:int64`; `mc:int64`; `pc:num`];;

let SI87_ATT_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc SI87_ATT_EXEC name
    ilist SI87_ATT_ALLOWED n;;

let SI87_ATT_MID = parse_term(
 "\\s. read SP s = fp /\\
      read X19 s = (if r = 24 then word 1 else word 0) /\\
      read X21 s = word_add fp (word 14336) /\\
      read X22 s = word_add fp (word 14448) /\\
      read X25 s = word_add fp (word 1984) /\\
      read (memory :> bytes32 (word_add fp (word 100))) s = word att /\\
      read (memory :> bytes64(word(pc + got_stack_chk_guard))) s = guard /\\
      read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
      read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
      read (memory :> bytes(ea,el)) s = ev /\\
      (r = 24
       ==> !t. t < 4627
               ==> read (memory :> bytes8 (word_add sig (word t))) s =
                   (" ^ string_of_term SI87_SIGATT ^ ") t)");;

(*** A stage post `0 < n ==> P` with n a numeral, as P ***)

let SI87_ATT_LT0_TAC =
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_imp c && is_comb(lhand c) &&
       (try fst(dest_const(rator(rator(lhand c)))) = "<" &&
            is_numeral(rand(lhand c)) && is_numeral(lhand(lhand c))
        with Failure _ -> false)
    then (try MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand c))) with Failure _ -> th)
    else th);;

let SI87_ATT_PC_TAC =
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read PC s = x`) (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NUM_LT_CONV THENC REWRITE_CONV[]) th else th) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `read PC s = x`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC;;

(*** The end of a path at join12: the frame and the events (the callees'  ***)
(*** memory safety split with the definitions of their event variables)   ***)

let SI87_PATH_END_TAC =
  SIGN_BETA_ALL_TAC THEN SIGN_SELECT_TAC THEN SIGN_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [SIGN_PATH_UNIFY_TAC; SI87_LOOP_MEMACCESS_TAC];;

let SI87_ATT_FIN_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN (SI87_MAYCHANGE_TAC ORELSE SI87_PATH_END_TAC);;

let SI87_ATT_TEMPLATE =
 `\(sig:int64) (sk:int64) (fp:int64) (rho:num) (att:num) (C:num) (r:num) (x:num->int32)
   (b:num->byte) (guard:int64) (mf:int64) (mc:int64) (pc:num).
   APPEND (f_ev_cl sig sk fp rho att C r x b guard mf mc pc)
    (APPEND
      (if r < 7 then f_ev_pz sig sk fp rho att C r x b guard mf mc pc
       else if r < 23
       then if EVEN (r - 7) then f_ev_pw1 sig sk fp rho att C r x b guard mf mc pc
            else f_ev_pw2 sig sk fp rho att C r x b guard mf mc pc
       else f_ev_pt sig sk fp rho att C r x b guard mf mc pc)
      (f_ev_hd sig sk fp rho att C r x b guard mf mc pc))
   :(uarch_event)list`;;

let SI87_ATT_SETUP_TAC =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,_ = CONJ_PAIR th in
    MAP_EVERY (fun (th,n) -> SI87_ASSUME_CALLEE_TAILED_TAC th n)
     [MP (SPEC_ALL SI87_HEAD) th,"H_HEAD"; MP (SPEC_ALL SI87_ZPRE) th,"H_ZPRE";
      MP (SPEC_ALL SI87_ZIT) th,"H_ZIT"; SI87_RPRE,"H_RPRE"; SI87_RIT,"H_RIT";
      SI87_TAIL,"H_TAIL"; MP (SPEC_ALL SI87_CLEAN) ms,"H_CLEAN"]) THEN
  CONCRETIZE_F_EVENTS_TAC SI87_ATT_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `sk:int64`; `skb:num->byte`; `fp:int64`;
    `rho:num`; `MU:num`; `RHO:num`; `att:num`; `C:num`; `r:num`; `x:num->int32`;
    `b:num->byte`; `guard:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst SI87_ATT_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SI87_ALIGNED16_32) THEN
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

(*** The challenge in the NTT domain at fp + 3072 in terms of C ***)

let SI87_ATT_CPH_TAC =
  FIRST_ASSUM(fun cth ->
    if can (term_match [] `num_of_bytelist l = (C:num)`) (concl cth) &&
       rhs(concl cth) = `C:num` then
      RULE_ASSUM_TAC(fun th ->
        let c = concl th in
        if can (find_term (fun t -> is_const t && fst(dest_const t) = "ensures")) c then th
        else if can (find_term (fun t -> is_const t && fst(dest_const t) = "mld_sign_cphat")) c
        then REWRITE_RULE[cth] (REWRITE_RULE[mld_sign_cphat] th) else th)
    else NO_TAC);;

(*** z_r fails, r < 7 ***)

let SI87_ATT_ZCASE_TAC =
  SUBGOAL_THEN `r <= 7 /\ ~(r = 24)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `r < 7` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `r < 7 ==> P`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SI87_ATT_CALL_TAC "H_ZPRE"
   [`r:num`; `sig:int64`; `sk:int64`; `skb:num->byte`; `fp:int64`; SI87_ATT_CPH;
    `RHO:num`; `att:num`; `pc:num`] 2 THEN
  SI87_ATT_PC_TAC THEN
  SI87_ATT_CALL_TAC "H_ZIT"
   [`F`; `sig:int64`; `sk:int64`; `skb:num->byte`; `fp:int64`; `r:num`; SI87_ATT_CPH;
    `RHO:num`; `att:num`; `pc:num`] 3 THEN
  SI87_ATT_PC_TAC THEN
  ARM_STEPS_TAC SI87_ATT_EXEC (4--5) THEN
  SI87_ATT_FIN_TAC;;

(*** check r - 7 of the rows fails, 7 <= r < 23 ***)

let SI87_ATT_ROWSLICE_TAC m st =
  MP_TAC(SPECL [`fp:int64`; `4096`; `2048`; `mld_poly_decompose_lo_32`; SI87_ATT_W; m; st]
               SIGN_ROW_SLICE) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [m; st]
             `!k. 256 * m <= k /\ k < 2048
                  ==> read (memory :> bytes32 (word_add fp (word (4096 + 4 * k)))) st = Q k`)
           (concl th)
    then REWRITE_TAC[th] else NO_TAC) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC];;

let SI87_ATT_WCASE_TAC =
  SUBGOAL_THEN `(r - 7) DIV 2 <= 8 /\ (r - 7) DIV 2 < 8 /\ ~(r = 24) /\
                2 * (r - 7) DIV 2 <= r - 7`
   STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `r < 23` THEN UNDISCH_TAC `7 <= r` THEN
    SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [SI87_ATT_R0; SI87_ATT_CT0; `261768`; `261888`; `r - 7`;
                `(r - 7) DIV 2`] SIGN_ROWS_GOOD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `j:num` o REWRITE_RULE[ASSUME `7 <= r`] o
      check (fun th -> can (term_match []
        `7 <= r ==> (!j. j < r - 7 /\ j < 16 ==> P j)`) (concl th))) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `j < r - 7` THEN UNDISCH_TAC `r < 23` THEN ARITH_TAC;
    DISCH_TAC] THEN
  SI87_ATT_CALL_TAC "H_ZPRE"
   [`7`; `sig:int64`; `sk:int64`; `skb:num->byte`; `fp:int64`; SI87_ATT_CPH;
    `RHO:num`; `att:num`; `pc:num`] 2 THEN
  SI87_ATT_PC_TAC THEN SI87_ATT_LT0_TAC THEN
  SI87_ATT_CALL_TAC "H_RPRE"
   [`(r - 7) DIV 2`; `sk:int64`; `skb:num->byte`; `fp:int64`; SI87_ATT_W; SI87_ATT_CPH;
    `pc:num`] 3 THEN
  SI87_ATT_PC_TAC THEN
  SI87_ATT_ROWSLICE_TAC `(r - 7) DIV 2` `s3:armstate` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `7 <= r /\ r < 23 ==> ~(P = word 0:int32)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `EVEN(r - 7)` THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `~(mld_poly_chknorm (if EVEN(r - 7) then a else b) (word w) = word 0)`)
      (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SI87_ATT_CALL_TAC "H_RIT"
     [`F`; `F`; `sk:int64`; `skb:num->byte`; `fp:int64`; `(r - 7) DIV 2`; SI87_ATT_W;
      SI87_ATT_CPH; `pc:num`] 4;
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `~(mld_poly_chknorm (if EVEN(r - 7) then a else b) (word w) = word 0)`)
      (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
     (SPECL [`7`; `r:num`] SIGN_ODD_ROW)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `r - 8` o REWRITE_RULE[ASSUME `7 <= r`] o
      check (fun th -> can (term_match []
        `7 <= r ==> (!j. j < r - 7 /\ j < 16 ==> P j)`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [UNDISCH_TAC `r < 23` THEN ARITH_TAC; DISCH_TAC] THEN
    SI87_ATT_CALL_TAC "H_RIT"
     [`T`; `F`; `sk:int64`; `skb:num->byte`; `fp:int64`; `(r - 7) DIV 2`; SI87_ATT_W;
      SI87_ATT_CPH; `pc:num`] 4] THEN
  SI87_ATT_PC_TAC THEN
  ARM_STEPS_TAC SI87_ATT_EXEC (5--6) THEN
  SI87_ATT_FIN_TAC;;

(*** the hints, r = 23 (too many) or 24 (success), both through TAIL ***)

let SI87_ATT_FACT_RW_TAC th =
  RULE_ASSUM_TAC(fun th' ->
    if can (find_term (fun t -> is_const t && fst(dest_const t) = "ensures")) (concl th') ||
       concl th' = concl th
    then th' else REWRITE_RULE[th] th');;

let SI87_ATT_TCASE_TAC =
  SUBGOAL_THEN `23 <= r /\ 7 <= 7` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(r < 23)` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [SI87_ATT_R0; SI87_ATT_CT0; `261768`; `261888`; `16`; `8`] SIGN_ROWS_GOOD) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[LE_REFL] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `j:num` o REWRITE_RULE[ASSUME `7 <= r`] o
      check (fun th -> can (term_match []
        `7 <= r ==> (!j. j < r - 7 /\ j < 16 ==> P j)`) (concl th))) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `23 <= r` THEN UNDISCH_TAC `j < 16` THEN ARITH_TAC;
    DISCH_TAC] THEN
  SI87_ATT_CALL_TAC "H_ZPRE"
   [`7`; `sig:int64`; `sk:int64`; `skb:num->byte`; `fp:int64`; SI87_ATT_CPH;
    `RHO:num`; `att:num`; `pc:num`] 2 THEN
  SI87_ATT_PC_TAC THEN SI87_ATT_LT0_TAC THEN
  SI87_ATT_CALL_TAC "H_RPRE"
   [`8`; `sk:int64`; `skb:num->byte`; `fp:int64`; SI87_ATT_W; SI87_ATT_CPH; `pc:num`] 3 THEN
  SI87_ATT_PC_TAC THEN SI87_ATT_LT0_TAC THEN
  SI87_ASM_RW_TAC[ARITH_RULE `256 * 8 = 2048`] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `(if 23 <= r then p else q) = (x:num->int32)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
    SI87_ATT_FACT_RW_TAC th THEN ASSUME_TAC th) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `(if 23 <= r then p else q) = (b:num->byte)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!j. j < 1024
        ==> read (memory :> bytes8 (word_add fp (word (12288 + j)))) s3 =
            (b:num->byte) j`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(fun th ->
      if is_var(rhs(concl th)) && name_of(rhs(concl th)) = "b"
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[mld_sign_hint_w1] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SI87_ATT_CALL_TAC "H_TAIL"
   [`sig:int64`; `fp:int64`; `C:num`; `x:num->int32`; `b:num->byte`; `pc:num`] 4 THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `23 <= r ==> (r = 24 <=> P)`) (concl th))) THEN
  ASM_REWRITE_TAC[NOT_LT] THEN DISCH_TAC THEN
  ASM_CASES_TAC `r = 24` THENL
   [SUBGOAL_THEN `mld_hint_count (mld_polyvec_make_hint_32 x b) 2048 <= 75` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if is_iff(concl th) && lhs(concl th) = `r = 24`
                            then ACCEPT_TAC(EQ_MP th (ASSUME `r = 24`)) else NO_TAC); ALL_TAC] THEN
    SI87_ATT_FACT_RW_TAC
      (ASSUME `mld_hint_count (mld_polyvec_make_hint_32 x b) 2048 <= 75`) THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [`sig:int64`; `C:num`] `read (memory :> bytes (sig,64)) s = C`)
             (concl th)
      then FIRST_ASSUM(fun cth ->
             if is_var(rhs(concl cth)) && name_of(rhs(concl cth)) = "C" &&
                can (term_match [] `num_of_bytelist l = (C:num)`) (concl cth)
             then ASSUME_TAC(MATCH_MP SIGN_BYTES8_OF_READ_BYTES (TRANS th (SYM cth)))
             else NO_TAC)
      else NO_TAC) THEN
    REPEAT(FIRST_X_ASSUM(fun th -> if concl th = `r = 24` then ASSUME_TAC(EQT_INTRO th)
                                   else NO_TAC)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(REWRITE_TAC[mld_sign_attempt_sig] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[mld_sign_cphat] THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `4627 = (64 + 7 * 640) + 83` SUBST1_TAC THENL
       [ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC SIGN_SIG_ASSEMBLE THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(ACCEPT_TAC o CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
        check (fun th -> can (term_match []
          `!t. t < 640 * 7
               ==> read (memory :> bytes8 (word_add sig (word (64 + t)))) s =
                   P t`) (concl th))) THEN NO_TAC) THEN
    (SI87_MAYCHANGE_TAC ORELSE SI87_PATH_END_TAC);
    SUBGOAL_THEN `~(mld_hint_count (mld_polyvec_make_hint_32 x b) 2048 <= 75)` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if is_iff(concl th) && lhs(concl th) = `r = 24`
                            then MP_TAC th else NO_TAC) THEN
      REWRITE_TAC[ASSUME `~(r = 24)`]; ALL_TAC] THEN
    SI87_ATT_FACT_RW_TAC
      (ASSUME `~(mld_hint_count (mld_polyvec_make_hint_32 x b) 2048 <= 75)`) THEN
    SI87_ATT_FIN_TAC];;

let SI87_ATT_PATHS_TAC =
  ASM_CASES_TAC `r < 7` THENL
   [SI87_ATT_ZCASE_TAC;
    SUBGOAL_THEN `7 <= r /\ 7 <= 7` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~(r < 7)` THEN ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `7 <= r ==> (!i. i < 7 ==> P i)`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_CASES_TAC `r < 23` THENL [SI87_ATT_WCASE_TAC; SI87_ATT_TCASE_TAC]];;

let SI87_ATT_CLEAN_TAC =
  FULL_INIT_TAC THEN
  SI87_ATT_CALL_TAC "H_CLEAN" [`r = 24`; `att:num`; `fp:int64`; `pc:num`] 1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  (SI87_MAYCHANGE_TAC ORELSE
   (SAFE_META_EXISTS_TAC allowed_vars_e THEN
    CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
    CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; SI87_LOOP_MEMACCESS_TAC]));;

let SI87_ATT = prove
 (SI87_ATT_STMT,
  SI87_ATT_SETUP_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa87_signature_internal_join12` SI87_ATT_MID THEN
  CONJ_TAC THENL
   [FULL_INIT_TAC THEN
    SI87_ATT_CALL_TAC "H_HEAD"
     [`fp:int64`; `att:num`; `rho:num`; `RHO:num`; `MU:num`; `C:num`; `guard:int64`;
      `pc:num`] 1 THEN
    SI87_ATT_CPH_TAC THEN SI87_ATT_PATHS_TAC;
    SI87_ATT_CLEAN_TAC]);;
