(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The stages of an attempt of mldsa44_signature_internal (clang 23 -O3 mono *)
(* reduced-RAM), as FULL lemmas for segments of the code at the frame rsp0   *)
(* of the attempt, following the parts of the gcc reduced-RAM proof          *)
(* (gcc12_O2_reduced_ram/signature_internal_44_proof.ml), with the region    *)
(* lemmas of signature_internal_44_inline.ml for the inlined code.           *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/signature_internal_44_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/signature_internal_44_inline.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_stage.ml";;
needs "x86/proofs/utils/mldsa_native_signing_rr.ml";;
needs "x86/proofs/utils/mldsa_native_lazy_matrix.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/lazy_eq_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The cleanup of an attempt (CLEAN), from join27 with RBX whose low byte is *)
(* 1 on success and 0 otherwise: the memsets of z (0xce0), the challenge     *)
(* (0x2500), w (0x1500), the packed w1 (0x720) and the polynomial of y       *)
(* (0x320), the zeroing of the structure of y (0x80) and of c~ (0x200), and *)
(* the test of BL: to join28 on success, else to the update of the count of *)
(* the attempts at +0x2828.                                                  *)
(* ------------------------------------------------------------------------- *)

let SI44_CLEAN_STMT = parse_term(subst_tokens ["@MC@",image_mc; "@NX@",string_of_int(layout "mldsa44_signature_internal" + 0x2828)]
 "!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e ok rsp0 rb0 pc.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          aligned 32 (rsp0:int64) /\\
          (word_zx (rb0:int64) = (word 0:byte) <=> ~ok) /\\
          ALL (nonoverlapping (word_sub rsp0 (word 8),10536))
              [(word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)]
          ==> ensures x86
               (\\s. bytes_loaded s (word pc) @MC@ /\\
                    read RIP s = word (pc + mldsa44_signature_internal_join27) /\\
                    read RSP s = rsp0 /\\ read RBX s = rb0 /\\
                    (read DF s <=> false) /\\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                    read (memory :> bytes(ea,el)) s = ev /\\
                    read events s = e)
               (\\s. read RIP s = (if ok then word (pc + mldsa44_signature_internal_join28)
                                  else word (pc + @NX@)) /\\
                    read RSP s = rsp0 /\\ read RBX s = rb0 /\\
                    (read DF s <=> false) /\\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                    read (memory :> bytes(ea,el)) s = ev /\\
                    (exists e2. read events s = APPEND e2 e /\\
                       e2 = f_events ok rsp0 mf pc /\\
                       memaccess_inbounds e2
                        [word_sub rsp0 (word 8),10536; word(pc + got_memset),8; ea,el]
                        [word_sub rsp0 (word 8),10536]))
               (MAYCHANGE [RSP; R14] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(word_sub rsp0 (word 8),8);
                           memory :> bytes(word_add rsp0 (word 0x80),16);
                           memory :> bytes(word_add rsp0 (word 0x200),32);
                           memory :> bytes(word_add rsp0 (word 0x320),1024);
                           memory :> bytes(word_add rsp0 (word 0x720),768);
                           memory :> bytes(word_add rsp0 (word 0xce0),1024);
                           memory :> bytes(word_add rsp0 (word 0x1500),4096);
                           memory :> bytes(word_add rsp0 (word 0x2500),1024)])");;

let SI44_CLEAN_EXEC = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
  [(layout "mldsa44_signature_internal_join27", layout "mldsa44_signature_internal" + 0x2828);
   layout_range "plt_memset"];;

let SI44_CLEAN = prove
 (SI44_CLEAN_STMT,
  (REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[memset_full_contract] th) "H_MEMSET") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(ok:bool) (rsp0:int64) (mf:int64) (pc:num).
      if ok then f_ev_ok rsp0 mf pc else f_ev_nok rsp0 mf pc:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `ok:bool`; `rsp0:int64`; `rb0:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst SI44_CLEAN_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SI_ALIGNED16_TAC [0x80; 0x200; 0x210] THEN
  GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
  FULL_INIT_TAC THEN
  RUN_STRAIGHT_TAC SI44_CLEAN_EXEC "H_MEMSET"
    (ref [`ok:bool`; `rsp0:int64`; `mf:int64`; `pc:num`])) THEN
  (SUBGOAL_THEN `word (val (rb0:int64) MOD 256):byte = word_zx rb0`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; VAL_EQ_0])) THENL
   [REWRITE_TAC[word_zx; GSYM VAL_EQ; VAL_WORD; DIMINDEX_8] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if is_iff(concl th) && free_in `ok:bool` (concl th)
                        then RULE_ASSUM_TAC(REWRITE_RULE[th]) else NO_TAC) THEN
  ASM_CASES_TAC `ok:bool` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> if concl th = `ok:bool` || concl th = `~ok`
     then RULE_ASSUM_TAC(fun th' -> if concl th' = concl th then th' else REWRITE_RULE[th] th') else NO_TAC) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_VAL_ADD_64; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  SI_DISCHARGE_TAC 8));;

(* ------------------------------------------------------------------------- *)
(* The packing of c~ and of the hints (TAIL), from the exit of the loop over *)
(* the rows (loop37_exit1): c~ (32 bytes at rsp0 + 0x200) copied to sig,    *)
(* the 84 bytes of the hints zeroed, and for each row k the unpacking of     *)
(* its w1 (W1UNPACK) and its hints (HROW). If the hints fit, the code sets   *)
(* BL to 1 and goes to the cleanup at join27 with the hints of               *)
(* mld_pack_hints at sig + 2336; otherwise to the rejection at join26.       *)
(* R15, the result, is set to 0 before the hints.                            *)
(* ------------------------------------------------------------------------- *)

let SI44_TAIL_STMT = parse_term(subst_tokens ["@MC@",image_mc]
 "exists f_events.
    forall e sig rsp0 rb0 (C:num) (x:num->int32) (b:num->byte) pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 32 rsp0 /\\
      nonoverlapping (sig,2420) (rsp0,10528) /\\
      ALL (nonoverlapping (word pc,libmldsa_size)) [(sig,2420); (rsp0,10528)]
      ==> ensures x86
           (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + mldsa44_signature_internal_loop37_exit1) /\\
                read RSP s = rsp0 /\\ read RBX s = rb0 /\\
                read (memory :> bytes64 (word_add rsp0 (word 8))) s = sig /\\
                read (memory :> bytes64 (word_add rsp0 (word 24))) s = word_add sig (word 2336) /\\
                read (memory :> bytes (word_add rsp0 (word 512),32)) s = C /\\
                (!j. j < 1024 ==> read (memory :> bytes32 (word_add rsp0 (word (5376 + 4 * j)))) s = x j) /\\
                (!j. j < 768 ==> read (memory :> bytes8 (word_add rsp0 (word (1824 + j)))) s = b j) /\\
                read events s = e)
           (\\s. read RIP s =
                (if mld_hint_count (mld_polyvec_make_hint_88 x b) 1024 <= 80
                 then word (pc + mldsa44_signature_internal_join27)
                 else word (pc + mldsa44_signature_internal_join26)) /\\
                read RSP s = rsp0 /\\ read R15 s = word 0 /\\
                (mld_hint_count (mld_polyvec_make_hint_88 x b) 1024 <= 80
                 ==> ~(word_zx (read RBX s) = (word 0:byte))) /\\
                read (memory :> bytes (sig,32)) s = C /\\
                (mld_hint_count (mld_polyvec_make_hint_88 x b) 1024 <= 80
                 ==> !t. t < 84
                         ==> read (memory :> bytes8 (word_add sig (word (2336 + t)))) s =
                             mld_pack_hints 80 4 (mld_polyvec_make_hint_88 x b) t) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events sig rsp0 pc x b /\\
                   memaccess_inbounds e2 [sig,2420; rsp0,10528] [sig,2420; rsp0,10528]))
           (MAYCHANGE [RIP; RAX; RBX; RCX; RDX; RSI; RDI; R8; R15] ,,
            MAYCHANGE [ZMM0; ZMM1] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(sig,32);
                       memory :> bytes(word_add sig (word 2336),84);
                       memory :> bytes(word_add rsp0 (word 800),1024)])");;
let SI44_TAIL_EXEC = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
  [(layout "mldsa44_signature_internal_loop37_exit1", layout "mldsa44_signature_internal" + 0x2851)];;
let TL_TEMPLATE =
 `\(sig:int64) (rsp0:int64) (pc:num) (x:num->int32) (b:num->byte).
   if mld_hint_count (mld_polyvec_make_hint_88 x b) 256 <= 80 then
    (if mld_hint_count (mld_polyvec_make_hint_88 x b) 512 <= 80 then
      (if mld_hint_count (mld_polyvec_make_hint_88 x b) 768 <= 80 then
        (if mld_hint_count (mld_polyvec_make_hint_88 x b) 1024 <= 80
         then f_ev_ok sig rsp0 pc x b else f_ev_r3 sig rsp0 pc x b)
       else f_ev_r2 sig rsp0 pc x b)
     else f_ev_r1 sig rsp0 pc x b)
   else f_ev_r0 sig rsp0 pc x b :(uarch_event)list`;;
let TL_ALLOWED = [`sig:int64`; `rsp0:int64`; `pc:num`; `x:num->int32`; `b:num->byte`];;
let TL_CALL_TAC name ilist n =
  REMOVE_THEN name (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (VM_MC,SI44_TAIL_EXEC,0x0,VM_MC,th)
      (`e:(uarch_event)list`::ilist) n THENL
     [VM_PRE_TAC TL_ALLOWED; LABEL_TAC name th]);;
let TL_B_SLICE_TAC k n =
  let ib = 1824 + 192 * k and wb = 192 * k in
  let st = mk_var("s"^string_of_int n,`:x86state`) in
  SUBGOAL_THEN (vsubst [st,`s:x86state`] (parse_term(Printf.sprintf
    "!j. j < 192 ==> read (memory :> bytes8 (word_add rsp0 (word (%d + j)))) s = b (%d + j)" ib wb)))
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC (parse_term(Printf.sprintf "%d + j" wb)) o check (fun th ->
      is_forall(concl th) && can (term_match [] `!j. j < 768 ==> read (memory :> bytes8 (word_add rsp0 (word (1824 + j)))) s = b j`) (concl th))) THEN
    REWRITE_TAC[ARITH_RULE(parse_term(Printf.sprintf "1824 + %d + j = %d + j" wb ib))] THEN
    DISCH_THEN MATCH_MP_TAC THEN UNDISCH_TAC `j < 192` THEN ARITH_TAC;
    ALL_TAC];;
let TL_X_SLICE_TAC k n =
  let w = 5376 + 1024 * k and p0 = 256 * k in
  let st = mk_var("s"^string_of_int n,`:x86state`) in
  SUBGOAL_THEN (vsubst [st,`s:x86state`] (parse_term(Printf.sprintf
    "!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4 * i)))) s = x (%d + i)" w p0)))
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC (parse_term(Printf.sprintf "%d + i" p0)) o check (fun th ->
      is_forall(concl th) && can (term_match [] `!j. j < 1024 ==> read (memory :> bytes32 (word_add rsp0 (word (5376 + 4 * j)))) s = x j`) (concl th))) THEN
    REWRITE_TAC[ARITH_RULE(parse_term(Printf.sprintf "5376 + 4 * (%d + i) = %d + 4 * i" p0 w))] THEN
    DISCH_THEN MATCH_MP_TAC THEN UNDISCH_TAC `i < 256` THEN ARITH_TAC;
    ALL_TAC];;
let TL_COUNT0_TAC =
  ASSUME_TAC(INST [`mld_polyvec_make_hint_88 x b`,`h:num->bool`] (CONJUNCT1 mld_hint_count)) THEN
  ASSUME_TAC(ARITH_RULE `0 <= 80`);;
let TL_CNT_TM p = subst [mk_small_numeral p,`p:num`] `mld_hint_count (mld_polyvec_make_hint_88 x b) p <= 80`;;
let TL_SPLIT_TAC p =
  let c = TL_CNT_TM p in
  ASM_CASES_TAC c THEN
  FIRST_ASSUM(fun th -> if concl th = c || concl th = mk_neg c
    then RULE_ASSUM_TAC(fun th' -> if concl th' = concl th then th' else REWRITE_RULE[th] th')
    else NO_TAC) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && free_in `RAX` (concl th)
                                then STRIP_ASSUME_TAC th else NO_TAC));;
let TL_FAIL_TAC p =
  SUBGOAL_THEN (mk_neg(TL_CNT_TM 1024)) ASSUME_TAC THENL
   [MP_TAC(SPECL [`mld_polyvec_make_hint_88 x b`; mk_small_numeral p; `1024`] MLD_HINT_COUNT_MONO) THEN
    FIRST_ASSUM(MP_TAC o check (fun th -> concl th = mk_neg(TL_CNT_TM p))) THEN ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;
let TL_ROW_TAC k n =
  let p1 = 256 * (k + 1) in
  X86_STEPS_TAC SI44_TAIL_EXEC (n--(n+2)) THEN TL_B_SLICE_TAC k (n+2) THEN
  TL_CALL_TAC ("H_W1U"^string_of_int k)
   [`word_add rsp0 (word 800):int64`; `rsp0:int64`; `pc:num`;
    parse_term(Printf.sprintf "\\t. (b:num->byte) (%d + t)" (192 * k))] (n+3) THEN
  X86_STEPS_TAC SI44_TAIL_EXEC ((n+4)--(n+5)) THEN TL_X_SLICE_TAC k (n+5) THEN
  TL_CALL_TAC ("H_HROW"^string_of_int k)
   [`x:num->int32`; `b:num->byte`; `sig:int64`; `rsp0:int64`; `pc:num`] (n+6) THEN
  TL_SPLIT_TAC p1 THENL [ALL_TAC; TL_FAIL_TAC p1];;
let TL_BL_NZ = prove
 (`!(h:56 word). ~(word_zx (word_join h (word 1:byte):int64) = (word 0:byte))`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;
let TL_PACK_TAC =
  X_GEN_TAC `t:num` THEN DISCH_TAC THEN REWRITE_TAC[mld_pack_hints] THEN
  CONV_TAC NUM_REDUCE_CONV THEN COND_CASES_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    SUBGOAL_THEN `t = 80 \/ t = 81 \/ t = 82 \/ t = 83` MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`t < 84`; `~(t < 80)`] THEN ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[]];;

let SI44_TAIL = prove
 (SI44_TAIL_STMT,
  (MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
   [SI44_W1U48,"H_W1U0"; SI44_W1U49,"H_W1U1"; SI44_W1U51,"H_W1U2"; SI44_W1U53,"H_W1U3";
    SI44_HROW0,"H_HROW0"; SI44_HROW1,"H_HROW1"; SI44_HROW2,"H_HROW2"; SI44_HROW3,"H_HROW3"] THEN
  CONCRETIZE_F_EVENTS_TAC TL_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `sig:int64`; `rsp0:int64`; `rb0:int64`; `C:num`;
                       `x:num->int32`; `b:num->byte`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; ALL; NONOVERLAPPING_CLAUSES; fst SI44_TAIL_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SI_ALIGNED16_TAC [0x200; 0x210] THEN
  GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
  FULL_INIT_TAC) THEN
  (MAP_EVERY (fun n ->
    MP_TAC(SPECL [`word_add rsp0 (word 512):int64`; `32`; `C:num`; mk_small_numeral n; `s0:x86state`]
             SIGN_BYTES128_OF_BYTES) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC) [0;1]) THEN
  (X86_STEPS_TAC SI44_TAIL_EXEC (1--12) THEN RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO; DIV_1])) THEN
  (SUBGOAL_THEN `C < 2 EXP (8 * 32)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes (word_add rsp0 (word 512),32)) s0 = C`) (concl th)
      then SUBST1_TAC(SYM th) else NO_TAC) THEN REWRITE_TAC[READ_BYTES_BOUND; READ_COMPONENT_COMPOSE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`sig:int64`; `C:num`; `2`; `s12:x86state`] SIGN_BYTES_OF_BYTES128) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0; DIV_1] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `C MOD 2 EXP (128 * 2) = C` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN FIRST_ASSUM(MP_TAC o check (fun th -> concl th = `C < 2 EXP (8 * 32)`)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN DISCH_TAC) THEN
  (MP_TAC(SPECL [`word_add sig (word 2336):int64`; `0`; `5`; `s12:x86state`] SIGN_BYTES_OF_BYTES128) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MOD_0] THEN CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  DISCH_THEN(fun th -> ASSUME_TAC(GEN `t:num`
    (REWRITE_RULE[GSYM(INST [`mld_polyvec_make_hint_88 x b`,`h:num->bool`] (CONJUNCT1 mld_hint_index));
                  WORD_RULE `word_add (word_add sig (word 2336)) (word t) = word_add sig (word (2336 + t))`]
      (SPEC `t:num` (MATCH_MP SIGN_BYTES8_ZERO th)))))) THEN
  (X86_STEPS_TAC SI44_TAIL_EXEC (13--16) THEN TL_B_SLICE_TAC 0 16 THEN
  TL_CALL_TAC "H_W1U0" [`word_add rsp0 (word 800):int64`; `rsp0:int64`; `pc:num`; `\t. (b:num->byte) (0 + t)`] 17) THEN
  (X86_STEPS_TAC SI44_TAIL_EXEC (18--21) THEN TL_X_SLICE_TAC 0 21 THEN TL_COUNT0_TAC THEN
  TL_CALL_TAC "H_HROW0" [`x:num->int32`; `b:num->byte`; `sig:int64`; `rsp0:int64`; `pc:num`] 22) THEN
  (TL_SPLIT_TAC 256 THENL [ALL_TAC; TL_FAIL_TAC 256]) THEN
  (TL_ROW_TAC 1 23) THEN
  (TL_ROW_TAC 2 30) THEN
  (TL_ROW_TAC 3 37) THEN
  (X86_STEPS_TAC SI44_TAIL_EXEC (44--45) THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[TL_BL_NZ]) THEN
  (CONJ_TAC THENL [TL_PACK_TAC; DISCHARGE_SAFETY_PROPERTY_TAC]));;

(* ------------------------------------------------------------------------- *)
(* s2 and t0 in the NTT domain, from the secret key skb, as the row          *)
(* iterations unpack and transform them, polynomial by polynomial (as in the *)
(* gcc proof, SIGN44_S2H and SIGN44_T0H).                                    *)
(* ------------------------------------------------------------------------- *)

let SI44_S2H =
 `mld_polyvec_map mld_poly_ntt
   (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte)(512 + j)))`;;

let SI44_T0H =
 `mld_polyvec_map mld_poly_ntt
   (mld_polyvec_unpack 416 mld_polyt0_unpack (\j. (skb:num->byte)(896 + j)))`;;

(* ------------------------------------------------------------------------- *)
(* One iteration of the loop over the rows of w0 (RIT), from loop37 with row *)
(* j in R13 and its address in RBX: s2_j unpacked into the scratch           *)
(* polynomial at rsp0 + 0x320 and transformed, its product with the          *)
(* challenge, w0_j - c s2_j in place and reduced, its norm check; then t0_j  *)
(* likewise, c t0_j reduced and checked, and the sum in place in row j. ok1  *)
(* and ok2 are the results of the two checks (ok2 matters only when ok1      *)
(* holds): if both pass, the code goes back to loop37 or, after the last     *)
(* row, to loop37_exit1, else to the rejection at join19. The callees (NTT,  *)
(* inverse NTT) use the stack below rsp0.                                    *)
(* ------------------------------------------------------------------------- *)

let RIT_ROW_ALIGNED = prove
 (`!rsp0:int64 j. aligned 32 rsp0 ==> aligned 16 (word_add rsp0 (word (5376 + 1024 * j)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ALIGNED_WORD_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC(MP (ISPECL [`16`;`32`;`rsp0:int64`] ALIGNED_WORD_WEAKEN)
                    (EQT_ELIM(DIVIDES_CONV `16 divides 32`))) THEN
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[];
      REWRITE_TAC[divides] THEN EXISTS_TAC `336 + 64 * j` THEN ARITH_TAC]]);;

let RIT_R0 = list_mk_comb(`mld_sign_r0`,
  [`mld_poly_decompose_lo_88`; `w:num->int32`; SI44_S2H; `cphat:num->int32`; `j:num`]);;
let RIT_CT0 = list_mk_comb(`mld_sign_ct0`, [SI44_T0H; `cphat:num->int32`; `j:num`]);;

let SI44_RIT_STMT = parse_term(subst_tokens
  ["@MC@",image_mc; "@R0@",string_of_term RIT_R0; "@CT0@",string_of_term RIT_CT0;
   "@FAIL@",string_of_int(layout "mldsa44_signature_internal_join19")]
 "exists f_events.
    forall e ok1 ok2 sk skb rsp0 j w cphat pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 32 rsp0 /\\ j < 4 /\\
      (ok1 <=> mld_poly_chknorm (@R0@) (word 95154) = word 0) /\\
      (ok1 ==> (ok2 <=> mld_poly_chknorm (@CT0@) (word 95232) = word 0)) /\\
      ALL (nonoverlapping (word_sub rsp0 (word 1471),11999))
          [(sk,2560); (word pc,libmldsa_size)]
      ==> ensures x86
           (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + mldsa44_signature_internal_loop37) /\\
                read RSP s = rsp0 /\\ read R13 s = word j /\\ read RCX s = word (2 + 96 * j) /\\
                read RBX s = word_add rsp0 (word (5376 + 1024 * j)) /\\
                read R12 s = word 0x0380200100000000 /\\
                read (memory :> bytes64 (word_add rsp0 (word 16))) s = word (12 + 416 * j) /\\
                read (memory :> bytes64 (word_add rsp0 (word 32))) s = word_add sk (word 512) /\\
                read (memory :> bytes64 (word_add rsp0 (word 64))) s = word_add sk (word 896) /\\
                (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (9472 + 4 * i)))) s =
                                 cphat i) /\\
                (!i. i < 2560 ==> read (memory :> bytes8 (word_add sk (word i))) s = skb i) /\\
                (!i. i < 256 ==> read (memory :> bytes32
                                   (word_add rsp0 (word ((5376 + 1024 * j) + 4 * i)))) s =
                                 mld_poly_decompose_lo_88 (mld_poly_of w j) i) /\\
                read events s = e)
           (\\s. read RIP s =
                (if ok1 /\\ ok2
                 then (if j + 1 < 4 then word (pc + mldsa44_signature_internal_loop37)
                       else word (pc + mldsa44_signature_internal_loop37_exit1))
                 else word (pc + @FAIL@)) /\\
                read RSP s = rsp0 /\\ read R12 s = word 0x0380200100000000 /\\
                (ok1 /\\ ok2
                 ==> read R13 s = word (j + 1) /\\ read RCX s = word (2 + 96 * (j + 1)) /\\
                     read RBX s = word_add rsp0 (word (5376 + 1024 * (j + 1))) /\\
                     read (memory :> bytes64 (word_add rsp0 (word 16))) s = word (12 + 416 * (j + 1)) /\\
                     (!i. i < 256 ==> read (memory :> bytes32
                                        (word_add rsp0 (word ((5376 + 1024 * j) + 4 * i)))) s =
                                      mld_poly_add (@R0@) (@CT0@) i)) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events ok1 ok2 sk rsp0 j pc /\\
                   memaccess_inbounds e2
                    [sk,2560; word_sub rsp0 (word 1471),11999;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa44_signature_internal_consts),32;
                     word(pc + mldsa_poly_ntt_consts),256;
                     word(pc + mldsa_poly_invntt_tomont_consts),448]
                    [word_sub rsp0 (word 1471),11999]))
           (MAYCHANGE [RSP; RBX; R12; R13; R14; R15] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(word_sub rsp0 (word 16),16);
                       memory :> bytes(word_add rsp0 (word 16),8);
                       memory :> bytes(word_add rsp0 (word 152),8);
                       memory :> bytes(word_add rsp0 (word 800),1024);
                       memory :> bytes(word_add rsp0 (word (5376 + 1024 * j)),1024)])");;

let SI44_RIT_EXEC = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
  [(layout "mldsa44_signature_internal_loop37", layout "mldsa44_signature_internal_loop37_exit1")];;

let RIT_TEMPLATE =
 `\(ok1:bool) (ok2:bool) (sk:int64) (rsp0:int64) (j:num) (pc:num).
   if ok1 then
    (if ok2 then (if j + 1 < 4 then f_ev_mid sk rsp0 j pc else f_ev_last sk rsp0 j pc)
     else f_ev_f2 sk rsp0 j pc)
   else f_ev_f1 sk rsp0 j pc :(uarch_event)list`;;

let RIT_CONSTS128 =
  map (fun n -> IMAGE_CONST_RULE_FOR VM_MC (layout n) 128)
   ["mldsa44_signature_internal_const1"; "mldsa44_signature_internal_const2"];;

let RIT_ALLOWED = [`ok1:bool`; `ok2:bool`; `sk:int64`; `rsp0:int64`; `j:num`; `pc:num`];;

let RIT_PRE_TAC =
  REPEAT CONJ_TAC THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(REWRITE_TAC[GSYM ADD_ASSOC] THEN FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
  VM_PRE_TAC RIT_ALLOWED;;

(* a region lemma at step n; a callee whose CALL is step n - 1 *)
let RIT_CALL_TAC name ilist n =
  REMOVE_THEN name (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (VM_MC,SI44_RIT_EXEC,0x0,VM_MC,th)
      (`e:(uarch_event)list`::ilist) n THENL
     [RIT_PRE_TAC; LABEL_TAC name th]);;

let RIT_FCALL_TAC name ilist n =
  RIT_CALL_TAC name
   (ilist @ [`pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]) n THEN
  RSP_NORM_TAC THEN EXPAND_CALLEE_MEMACCESS_TAC;;

(* the two RIP-relative loads of 2^22 and -q into XMM5 and XMM6 after state n,
   the second ending at fn + r + 8 *)
let RIT_RCONST_TAC n r =
  YMM_GHOST_TAC (mk_var("s"^string_of_int n,`:x86state`))
    [("YMM5","ymm5_"^string_of_int n); ("YMM6","ymm6_"^string_of_int n)] THEN
  IMAGE_RIPREL_TAC (el 0 RIT_CONSTS128) (layout "mldsa44_signature_internal" + r) THEN
  IMAGE_RIPREL_TAC (el 1 RIT_CONSTS128) (layout "mldsa44_signature_internal" + r + 8);;

let RIT_B = `word_add rsp0 (word (5376 + 1024 * j)):int64`;;
let RIT_S2I = mk_comb(mk_comb(`mld_poly_of`,SI44_S2H),`j:num`);;
let RIT_T0I = mk_comb(mk_comb(`mld_poly_of`,SI44_T0H),`j:num`);;
let RIT_PW1 = list_mk_comb(`mld_poly_pointwise_montgomery`,[RIT_S2I; `cphat:num->int32`]);;
let RIT_PW2 = list_mk_comb(`mld_poly_pointwise_montgomery`,[RIT_T0I; `cphat:num->int32`]);;
let RIT_W0J = `mld_poly_decompose_lo_88 (mld_poly_of (w:num->int32) j)`;;
let RIT_CS2 = mk_comb(`mld_poly_invntt_tomont`,RIT_PW1);;
let RIT_SUBX = list_mk_comb(`mld_poly_sub`,[RIT_W0J; RIT_CS2]);;

(* bytes off .. off + n - 1 of the secret key at state st *)
let RIT_SLICE_TAC off n st =
  MP_TAC(SPECL [`sk:int64`; `skb:num->byte`; `2560`; off; n; st] SIGN_SK_SLICE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `j < 4` THEN ARITH_TAC; DISCH_TAC];;

(* the checks as (P <=> ok), so that rewriting with them keeps ok1 and ok2 *)
let RIT_ORIENT_TAC =
  FIRST_X_ASSUM(fun th -> if is_iff(concl th) && lhs(concl th) = `ok1:bool`
                          then ASSUME_TAC(GSYM th) else NO_TAC) THEN
  FIRST_X_ASSUM(fun th -> if is_imp(concl th) && lhand(concl th) = `ok1:bool`
                          then ASSUME_TAC(CONV_RULE(RAND_CONV SYM_CONV) th) else NO_TAC);;

(* the branch on a norm check (test eax, eax; jne) in the PC and in the events,
   as ok, from (mld_poly_chknorm x b = word 0 <=> ok), which is then dropped *)
let RIT_DECIDE_TAC okv =
  FIRST_X_ASSUM(fun th ->
    if is_iff(concl th) && rhs(concl th) = okv then
      RULE_ASSUM_TAC(fun th' ->
        if can (term_match [] `read RIP s = x`) (concl th') ||
           can (term_match [] `read events s = x`) (concl th')
        then REWRITE_RULE[th] (REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0; WORD_AND_REFL] th')
        else th')
    else NO_TAC);;

let RIT_MAYCHANGE_TAC =
  W(fun (asl,w) -> if maychange_term w then ALL_TAC else NO_TAC) THEN
  SI_FB_NORM_TAC 1471 THEN
  FIRST_X_ASSUM(fun th -> if maychange_term (concl th) && not(is_forall(concl th))
                          then MP_TAC th else NO_TAC) THEN
  DISCH_TAC THEN MONOTONE_MAYCHANGE_TAC;;

let RIT_END_TAC = REPEAT CONJ_TAC THEN (RIT_MAYCHANGE_TAC ORELSE SI_DISCHARGE_TAC 1471);;

(* a failed check: to join19 *)
let RIT_FAIL_TAC okv =
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read RIP s = x`) (concl th)
                           then REWRITE_RULE[ASSUME(mk_neg okv)] th else th) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN RIT_END_TAC;;

let RIT_TEST4 = prove
 (`!j. j < 4 ==> (val(word (j + 18446744073709551613):int64) = 0 <=> ~(j + 1 < 4))`,
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC NUM_REDUCE_CONV);;

(*** w0_j - c s2_j: steps 1 to 27 ***)

let RIT_PART1_TAC =
  X86_STEPS_TAC SI44_RIT_EXEC (1--5) THEN
  RIT_SLICE_TAC `512 + 96 * j` `96` `s5:x86state` THEN
  RIT_CALL_TAC "H_ETA" [`word_add sk (word (512 + 96 * j)):int64`; `rsp0:int64`; `pc:num`;
                        `\i. (skb:num->byte)((512 + 96 * j) + i)`] 6 THEN
  SIGN_UNPACK_POLY_OF_TAC `mld_polyeta_unpack_2` THEN
  X86_STEPS_TAC SI44_RIT_EXEC (7--8) THEN
  RIT_FCALL_TAC "H_NTT" [`read RDI s`;
    `mld_poly_of (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte)(512 + j))) j`] 9 THEN
  SIGN_NTT_POLY_OF_TAC THEN
  X86_STEPS_TAC SI44_RIT_EXEC (10--11) THEN
  RIT_CALL_TAC "H_PWM1" [`rsp0:int64`; `pc:num`; RIT_S2I; `cphat:num->int32`] 12 THEN
  X86_STEPS_TAC SI44_RIT_EXEC (13--14) THEN
  RIT_FCALL_TAC "H_INV" [`read RDI s`; RIT_PW1] 15 THEN
  X86_STEPS_TAC SI44_RIT_EXEC (16--17) THEN
  RIT_CALL_TAC "H_SUB" [RIT_B; `rsp0:int64`; `pc:num`; RIT_W0J; RIT_CS2] 18 THEN
  X86_STEPS_TAC SI44_RIT_EXEC (19--19) THEN RIT_RCONST_TAC 19 0x1f0b THEN
  X86_STEPS_TAC SI44_RIT_EXEC (20--22) THEN
  RIT_CALL_TAC "H_RED1" [RIT_B; `pc:num`; RIT_SUBX] 23 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_r0]) THEN
  X86_STEPS_TAC SI44_RIT_EXEC (24--26) THEN
  RIT_CALL_TAC "H_CHK1" [RIT_B; `pc:num`; RIT_R0] 27;;

(*** c t0_j, once the first check passed: steps 30 to 51 ***)

let RIT_PART2_TAC =
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read RIP s = x`) (concl th)
                           then REWRITE_RULE[ASSUME `ok1:bool`] th else th) THEN
  FIRST_X_ASSUM(fun th -> if is_imp(concl th) && lhand(concl th) = `ok1:bool`
                          then ASSUME_TAC(MP th (ASSUME `ok1:bool`)) else NO_TAC) THEN
  X86_STEPS_TAC SI44_RIT_EXEC (30--33) THEN
  RIT_SLICE_TAC `896 + 416 * j` `416` `s33:x86state` THEN
  RIT_CALL_TAC "H_T0U" [`word_add sk (word (896 + 416 * j)):int64`; `rsp0:int64`; `pc:num`;
                        `\i. (skb:num->byte)((896 + 416 * j) + i)`] 34 THEN
  SIGN_UNPACK_POLY_OF_TAC `mld_polyt0_unpack` THEN
  X86_STEPS_TAC SI44_RIT_EXEC (35--36) THEN
  RIT_FCALL_TAC "H_NTT" [`read RDI s`;
    `mld_poly_of (mld_polyvec_unpack 416 mld_polyt0_unpack (\j. (skb:num->byte)(896 + j))) j`] 37 THEN
  SIGN_NTT_POLY_OF_TAC THEN
  X86_STEPS_TAC SI44_RIT_EXEC (38--39) THEN
  RIT_CALL_TAC "H_PWM2" [`rsp0:int64`; `pc:num`; RIT_T0I; `cphat:num->int32`] 40 THEN
  X86_STEPS_TAC SI44_RIT_EXEC (41--42) THEN
  RIT_FCALL_TAC "H_INV" [`read RDI s`; RIT_PW2] 43 THEN
  X86_STEPS_TAC SI44_RIT_EXEC (44--44) THEN RIT_RCONST_TAC 44 0x228b THEN
  X86_STEPS_TAC SI44_RIT_EXEC (45--47) THEN
  RIT_CALL_TAC "H_RED2" [`rsp0:int64`; `pc:num`; mk_comb(`mld_poly_invntt_tomont`,RIT_PW2)] 48 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_ct0]) THEN
  X86_STEPS_TAC SI44_RIT_EXEC (49--50) THEN
  RIT_CALL_TAC "H_CHK2" [`rsp0:int64`; `pc:num`; RIT_CT0] 51;;

(*** the sum, once both checks passed, and the back edge: steps 54 to 63 ***)

let RIT_PART3_TAC =
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read RIP s = x`) (concl th)
                           then REWRITE_RULE[ASSUME `ok2:bool`] th else th) THEN
  X86_STEPS_TAC SI44_RIT_EXEC (54--55) THEN
  RIT_CALL_TAC "H_ADD" [RIT_B; `rsp0:int64`; `pc:num`; RIT_CT0; RIT_R0] 56 THEN
  X86_STEPS_TAC SI44_RIT_EXEC (57--63) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP RIT_TEST4 (ASSUME `j < 4`)]) THEN
  ASM_CASES_TAC `j + 1 < 4` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  RIT_END_TAC;;

let SI44_RIT = prove
 (SI44_RIT_STMT,
  MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
   [SI44_ETA38,"H_ETA"; SI44_PWM39,"H_PWM1"; SI44_SUB40,"H_SUB"; SI44_RED41,"H_RED1";
    SI44_CHK42,"H_CHK1"; SI44_T0U43,"H_T0U"; SI44_PWM44,"H_PWM2"; SI44_RED45,"H_RED2";
    SI44_CHK46,"H_CHK2"; SI44_ADD47,"H_ADD";
    MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_NTT";
    MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_INV"] THEN
  CONCRETIZE_F_EVENTS_TAC RIT_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `ok1:bool`; `ok2:bool`; `sk:int64`; `skb:num->byte`;
    `rsp0:int64`; `j:num`; `w:num->int32`; `cphat:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES; fst SI44_RIT_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  RIT_ORIENT_TAC THEN SI_ALIGNED16_TAC [0x320; 0x2500] THEN
  MP_TAC(SPECL [`rsp0:int64`; `j:num`] RIT_ROW_ALIGNED) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  FULL_INIT_TAC THEN RIT_PART1_TAC THEN
  X86_STEPS_TAC SI44_RIT_EXEC (28--29) THEN RIT_DECIDE_TAC `ok1:bool` THEN
  ASM_CASES_TAC `ok1:bool` THENL [ALL_TAC; RIT_FAIL_TAC `ok1:bool`] THEN
  RIT_PART2_TAC THEN
  X86_STEPS_TAC SI44_RIT_EXEC (52--53) THEN RIT_DECIDE_TAC `ok2:bool` THEN
  ASM_CASES_TAC `ok2:bool` THENL [ALL_TAC; RIT_FAIL_TAC `ok2:bool`] THEN
  RIT_PART3_TAC);;

(* ------------------------------------------------------------------------- *)
(* The loop over the rows of w0, for the first m rows, both of whose checks  *)
(* pass (RPRE), from the exit of the loop over z (+0x1c8d), where the code   *)
(* sets up row 0, as gcc's SIGN44_RPRE: row j of w holds w0_j - c s2_j +     *)
(* c t0_j afterwards (mld_sign_hint_x), the rows after the first m are      *)
(* unchanged.                                                                *)
(* ------------------------------------------------------------------------- *)

let RPRE_R0 = list_mk_comb(`mld_sign_r0`,
  [`mld_poly_decompose_lo_88`; `w:num->int32`; SI44_S2H; `cphat:num->int32`; `j:num`]);;
let RPRE_CT0 = list_mk_comb(`mld_sign_ct0`, [SI44_T0H; `cphat:num->int32`; `j:num`]);;
let RPRE_HX = list_mk_comb(`mld_sign_hint_x 4 mld_poly_decompose_lo_88`,
  [`w:num->int32`; SI44_S2H; SI44_T0H; `cphat:num->int32`]);;

let SI44_RSTART = layout "mldsa44_signature_internal" + 0x1c8d;;

let SI44_RPRE_STMT = parse_term(subst_tokens
  ["@MC@",image_mc; "@R0@",string_of_term RPRE_R0; "@CT0@",string_of_term RPRE_CT0;
   "@HX@",string_of_term RPRE_HX; "@START@",string_of_int SI44_RSTART]
 "exists f_events.
    forall e m sk skb rsp0 w cphat pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 32 rsp0 /\\ m <= 4 /\\
      (!j. j < m ==> mld_poly_chknorm (@R0@) (word 95154) = word 0 /\\
                     mld_poly_chknorm (@CT0@) (word 95232) = word 0) /\\
      ALL (nonoverlapping (word_sub rsp0 (word 1471),11999))
          [(sk,2560); (word pc,libmldsa_size)]
      ==> ensures x86
           (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + @START@) /\\
                read RSP s = rsp0 /\\
                read R12 s = word 0x0380200100000000 /\\
                read (memory :> bytes64 (word_add rsp0 (word 32))) s = word_add sk (word 512) /\\
                read (memory :> bytes64 (word_add rsp0 (word 64))) s = word_add sk (word 896) /\\
                (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (9472 + 4 * i)))) s =
                                 cphat i) /\\
                (!i. i < 2560 ==> read (memory :> bytes8 (word_add sk (word i))) s = skb i) /\\
                (!i. i < 1024 ==> read (memory :> bytes32 (word_add rsp0 (word (5376 + 4 * i)))) s =
                                  mld_polyvec_map mld_poly_decompose_lo_88 w i) /\\
                read events s = e)
           (\\s. read RIP s =
                (if m < 4 then word (pc + mldsa44_signature_internal_loop37)
                 else word (pc + mldsa44_signature_internal_loop37_exit1)) /\\
                read RSP s = rsp0 /\\ read R12 s = word 0x0380200100000000 /\\
                read R13 s = word m /\\ read RCX s = word (2 + 96 * m) /\\
                read RBX s = word_add rsp0 (word (5376 + 1024 * m)) /\\
                read (memory :> bytes64 (word_add rsp0 (word 16))) s = word (12 + 416 * m) /\\
                (!i. i < 256 * m ==> read (memory :> bytes32 (word_add rsp0 (word (5376 + 4 * i)))) s =
                                     @HX@ i) /\\
                (!i. 256 * m <= i /\\ i < 1024
                     ==> read (memory :> bytes32 (word_add rsp0 (word (5376 + 4 * i)))) s =
                         mld_polyvec_map mld_poly_decompose_lo_88 w i) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events m sk rsp0 pc /\\
                   memaccess_inbounds e2
                    [sk,2560; word_sub rsp0 (word 1471),11999;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa44_signature_internal_consts),32;
                     word(pc + mldsa_poly_ntt_consts),256;
                     word(pc + mldsa_poly_invntt_tomont_consts),448]
                    [word_sub rsp0 (word 1471),11999]))
           (MAYCHANGE [RSP; RBX; R12; R13; R14; R15] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(word_sub rsp0 (word 16),16);
                       memory :> bytes(word_add rsp0 (word 16),8);
                       memory :> bytes(word_add rsp0 (word 152),8);
                       memory :> bytes(word_add rsp0 (word 800),1024);
                       memory :> bytes(word_add rsp0 (word 5376),4096)])");;

let SI44_RPRE_EXEC = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
  [(SI44_RSTART, layout "mldsa44_signature_internal_loop37_exit1")];;

let RPRE_INV = parse_term(subst_tokens ["@HX@",string_of_term RPRE_HX]
 "\\i s. read RSP s = rsp0 /\\ read R12 s = word 0x0380200100000000 /\\
       read R13 s = word i /\\ read RCX s = word (2 + 96 * i) /\\
       read RBX s = word_add rsp0 (word (5376 + 1024 * i)) /\\
       read (memory :> bytes64 (word_add rsp0 (word 16))) s = word (12 + 416 * i) /\\
       read (memory :> bytes64 (word_add rsp0 (word 32))) s = word_add sk (word 512) /\\
       read (memory :> bytes64 (word_add rsp0 (word 64))) s = word_add sk (word 896) /\\
       (!k. k < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (9472 + 4 * k)))) s =
                        cphat k) /\\
       (!k. k < 2560 ==> read (memory :> bytes8 (word_add sk (word k))) s = skb k) /\\
       (!k. k < 256 * i ==> read (memory :> bytes32 (word_add rsp0 (word (5376 + 4 * k)))) s =
                            @HX@ k) /\\
       (!k. 256 * i <= k /\\ k < 1024
            ==> read (memory :> bytes32 (word_add rsp0 (word (5376 + 4 * k)))) s =
                mld_polyvec_map mld_poly_decompose_lo_88 w k)");;

(* the PC after row i of the first m <= 4 rows, from that of RIT *)
let RPRE_PC = prove
 (`!i m a b. i < m /\ m <= 4
             ==> (if i + 1 < 4 then word a else word b):int64 =
                 word (if i + 1 < m then a else if m < 4 then a else b)`,
  REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMPLE_ARITH_TAC);;

let RPRE_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `i < 4` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    can (term_match [] `!j. j < m ==> P j /\ Q j`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FULL_INIT_TAC THEN
  MP_TAC(SPECL [`rsp0:int64`; `5376`; `1024`; `mld_poly_decompose_lo_88`;
                `w:num->int32`; `i:num`; `s0:x86state`] SIGN_ROW_SLICE) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [`i:num`; `s0:x86state`]
             `!k. 256 * i <= k /\ k < 1024
                  ==> read (memory :> bytes32 (word_add rsp0 (word (5376 + 4 * k)))) s0 = Q k`)
           (concl th)
    then REWRITE_TAC[th] else NO_TAC) THEN
  ANTS_TAC THENL [UNDISCH_TAC `i < 4` THEN ARITH_TAC; STRIP_TAC] THEN
  REMOVE_THEN "H_RIT" (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (VM_MC,SI44_RPRE_EXEC,0x0,VM_MC,th)
      [`e:(uarch_event)list`; `T`; `T`; `sk:int64`; `skb:num->byte`; `rsp0:int64`; `i:num`;
       `w:num->int32`; `cphat:num->int32`; `pc:num`] 1 THENL
     [REPEAT CONJ_TAC THEN TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
      VM_PRE_TAC [`sk:int64`; `rsp0:int64`; `i:num`; `pc:num`];
      LABEL_TAC "H_RIT" th]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP RPRE_PC (CONJ (ASSUME `i < m`) (ASSUME `m <= 4`))]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SIGN_ROW_JOIN THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
  SIGN_LOOP_DISCHARGE_TAC;;

let SI44_RPRE = prove
 (SI44_RPRE_STMT,
  SI_ASSUME_CALLEE_TAILED_TAC SI44_RIT "H_RIT" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(m:num) (sk:int64) (rsp0:int64) (pc:num).
     APPEND (f_ev_back m sk rsp0 pc)
      (APPEND (ENUMERATEL m (\i. f_ev_rit sk rsp0 pc i)) (f_ev_front sk rsp0 pc))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `m:num`; `sk:int64`; `skb:num->byte`;
    `rsp0:int64`; `w:num->int32`; `cphat:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst SI44_RPRE_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `0 < m` THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `m:num`
     `pc + mldsa44_signature_internal_loop37`
     `if m < 4 then pc + mldsa44_signature_internal_loop37
      else pc + mldsa44_signature_internal_loop37_exit1`
     RPRE_INV THEN
    REPEAT CONJ_TAC THENL
     [SIMPLE_ARITH_TAC;
      REWRITE_TAC[CONJUNCT1 LT; MULT_CLAUSES; ADD_CLAUSES; LE_0] THEN
      FULL_INIT_TAC THEN X86_STEPS_TAC SI44_RPRE_EXEC (1--6) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN
      SI_DISCHARGE_TAC 1471;
      RPRE_BODY_TAC;
      REWRITE_TAC[] THEN FULL_INIT_TAC THEN SIGN_PC_COND_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      SIGN_BETA_ALL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC];
    SUBGOAL_THEN `m = 0` SUBST_ALL_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN X86_STEPS_TAC SI44_RPRE_EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ARITH; MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    REWRITE_TAC[ENUMERATEL; APPEND; APPEND_NIL] THEN SI_DISCHARGE_TAC 1471]);;

(* ------------------------------------------------------------------------- *)
(* s1 in the NTT domain and y, as in the gcc proof (SIGN44_S1H, SIGN44_YK).   *)
(* ------------------------------------------------------------------------- *)

let SI44_S1H =
 `mld_polyvec_map mld_poly_ntt
   (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte)(128 + j)))`;;

let SI44_YK = `mld_sign_y mld_poly_uniform_gamma1_17 rhop kappa`;;

(* ------------------------------------------------------------------------- *)
(* One iteration of the loop over z (ZIT), from join11 with i in R13: s1_i   *)
(* unpacked into z at rsp0 + 0xce0 and transformed, its product with the     *)
(* challenge, y_i sampled again (absorbing rho'' || kappa + i, squeezing,    *)
(* unpacking at rsp0 + 0x320 and zeroing the state), z_i = c s1_i + y_i      *)
(* reduced, its norm check (ok), and, if it passes, z_i packed into the      *)
(* signature at sig + 32 + 576 i; then back to join11 or, after the last,    *)
(* to the setup of the rows (+0x1c8d); a failed check goes to the rejection  *)
(* at join26. R15 is 0 on all exits.                                         *)
(* ------------------------------------------------------------------------- *)

let ZIT_ZI = list_mk_comb(`mld_sign_z`, [SI44_S1H; `cphat:num->int32`; SI44_YK; `i:num`]);;

let SI44_ZNEXT = layout "mldsa44_signature_internal" + 0x1c8d;;

let SI44_ZIT_STMT = parse_term(subst_tokens
  ["@MC@",image_mc; "@ZI@",string_of_term ZIT_ZI; "@NEXT@",string_of_int SI44_ZNEXT]
 "!mf mc ea el ev.
     memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e ok sig sk skb rsp0 rhop kappa i cphat pc.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          aligned 32 rsp0 /\\ i < 4 /\\
          (mld_poly_chknorm (@ZI@) (word 130994) = word 0 <=> ok) /\\
          ALL (nonoverlapping (word_sub rsp0 (word 1471),11999))
              [(sig,2420); (sk,2560); (word pc,libmldsa_size);
               (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\\
          ALL (nonoverlapping (sig,2420))
              [(sk,2560); (word pc,libmldsa_size);
               (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
           (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + mldsa44_signature_internal_join11) /\\
                read RSP s = rsp0 /\\ read R13 s = word i /\\ read RCX s = word (2 + 96 * i) /\\
                read R10 s = word_add sig (word (39 + 576 * i)) /\\
                read R12 s = word 0x0380200100000000 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes64 (word_add rsp0 (word 96))) s = word_add sk (word 128) /\\
                read (memory :> bytes64 (word_add rsp0 (word 128))) s = word_add rsp0 (word 736) /\\
                read (memory :> bytes16 (word_add rsp0 (word 136))) s = word kappa /\\
                read (memory :> bytes (word_add rsp0 (word 736),64)) s = rhop /\\
                (!k. k < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (9472 + 4 * k)))) s =
                                 cphat k) /\\
                (!k. k < 2560 ==> read (memory :> bytes8 (word_add sk (word k))) s = skb k) /\\
                read events s = e)
           (\\s. read RIP s =
                (if ok then (if i + 1 < 4 then word (pc + mldsa44_signature_internal_join11)
                             else word (pc + @NEXT@))
                 else word (pc + mldsa44_signature_internal_join26)) /\\
                read RSP s = rsp0 /\\ read R12 s = word 0x0380200100000000 /\\
                read R15 s = word 0 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                (ok ==> read R13 s = word (i + 1) /\\ read RCX s = word (2 + 96 * (i + 1)) /\\
                        read R10 s = word_add sig (word (39 + 576 * (i + 1))) /\\
                        (!j. j < 576 ==> read (memory :> bytes8 (word_add sig (word (32 + 576 * i + j)))) s =
                                         mld_polyz_pack_17 (@ZI@) j)) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events ok sig sk rsp0 i mf mc pc /\\
                   memaccess_inbounds e2
                    [sig,2420; sk,2560; word_sub rsp0 (word 1471),11999;
                     word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa44_signature_internal_consts),32;
                     word(pc + mldsa_poly_ntt_consts),256;
                     word(pc + mldsa_poly_invntt_tomont_consts),448]
                    [sig,2420; word_sub rsp0 (word 1471),11999]))
           (MAYCHANGE [RSP; RBX; R10; R12; R13; R14; R15] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(word_sub rsp0 (word 296),296);
                       memory :> bytes(word_add rsp0 (word 16),8);
                       memory :> bytes(word_add rsp0 (word 152),8);
                       memory :> bytes(word_add rsp0 (word 160),208);
                       memory :> bytes(word_add rsp0 (word 408),8);
                       memory :> bytes(word_add rsp0 (word 416),66);
                       memory :> bytes(word_add rsp0 (word 800),1024);
                       memory :> bytes(word_add rsp0 (word 2592),680);
                       memory :> bytes(word_add rsp0 (word 3296),1024);
                       memory :> bytes(word_add sig (word (32 + 576 * i)),576)])");;

let SI44_ZIT_EXEC = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
  [(layout "mldsa44_signature_internal_join11", SI44_ZNEXT);
   layout_range "plt_memset"; layout_range "plt_memcpy"];;

let ZIT_TEMPLATE =
 `\(ok:bool) (sig:int64) (sk:int64) (rsp0:int64) (i:num) (mf:int64) (mc:int64) (pc:num).
   if ok then (if i + 1 < 4 then f_ev_mid sig sk rsp0 i mf mc pc else f_ev_last sig sk rsp0 i mf mc pc)
   else f_ev_f sig sk rsp0 i mf mc pc :(uarch_event)list`;;

let ZIT_ALLOWED = [`ok:bool`; `sig:int64`; `sk:int64`; `rsp0:int64`; `i:num`; `mf:int64`; `mc:int64`; `pc:num`];;

(* a fact for j < n from one for a larger bound *)
let SI_BOUND_TAC =
  W(fun (asl,w) ->
    let v,bd = dest_forall w in
    let ant = lhand bd in
    X_GEN_TAC v THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN UNDISCH_TAC ant THEN ARITH_TAC));;

let ZIT_CALL_TAC name ilist n =
  REMOVE_THEN name (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (VM_MC,SI44_ZIT_EXEC,0x0,VM_MC,th)
      (`e:(uarch_event)list`::ilist) n THENL
     [REPEAT CONJ_TAC THEN
      TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
      TRY(REWRITE_TAC[GSYM ADD_ASSOC] THEN FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
      TRY(SI_BOUND_TAC THEN NO_TAC) THEN
      TRY(REWRITE_TAC[XMM7; READ_COMPONENT_COMPOSE; READ_ZEROTOP_128] THEN
          ASM_REWRITE_TAC[VM_ZX_JOIN] THEN CONV_TAC WORD_REDUCE_CONV THEN NO_TAC) THEN
      VM_PRE_TAC ZIT_ALLOWED;
      LABEL_TAC name th]);;

let ZIT_FCALL_TAC name ilist n =
  ZIT_CALL_TAC name
   (ilist @ [`pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]) n THEN
  RSP_NORM_TAC THEN EXPAND_CALLEE_MEMACCESS_TAC;;

(* the PC after a region lemma whose exit is fn + k, as one numeral *)
let SI_RIP_NORM_TAC =
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read RIP s = x`) (concl th)
                           then CONV_RULE(DEPTH_CONV NUM_ADD_CONV) th else th);;

let ZIT_SLICE_TAC off n st =
  MP_TAC(SPECL [`sk:int64`; `skb:num->byte`; `2560`; off; n; st] SIGN_SK_SLICE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `i < 4` THEN ARITH_TAC; DISCH_TAC];;

let ZIT_CONSTS128 = RIT_CONSTS128;;

(* the RIP-relative loads of 2^22 and -q into XMM6 and XMM7 after state n *)
let ZIT_RCONST_TAC n r =
  YMM_GHOST_TAC (mk_var("s"^string_of_int n,`:x86state`))
    [("YMM6","ymm6_"^string_of_int n); ("YMM7","ymm7_"^string_of_int n)] THEN
  IMAGE_RIPREL_TAC (el 0 ZIT_CONSTS128) (layout "mldsa44_signature_internal" + r) THEN
  IMAGE_RIPREL_TAC (el 1 ZIT_CONSTS128) (layout "mldsa44_signature_internal" + r + 8);;

let ZIT_S1I = mk_comb(mk_comb(`mld_poly_of`,SI44_S1H),`i:num`);;
let ZIT_PW = list_mk_comb(`mld_poly_pointwise_montgomery`,[ZIT_S1I; `cphat:num->int32`]);;
let ZIT_CS1 = mk_comb(`mld_poly_invntt_tomont`,ZIT_PW);;
let ZIT_YI = mk_comb(mk_comb(`mld_poly_of`,SI44_YK),`i:num`);;
let ZIT_M = `rhop + 2 EXP 512 * val(word(kappa + i):int16)`;;
let ZIT_S = mk_comb(`mld_keccak_absorb_once 136 0x1F 66`,ZIT_M);;

let ZIT_MAYCHANGE_TAC =
  W(fun (asl,w) -> if maychange_term w then ALL_TAC else NO_TAC) THEN
  SI_FB_NORM_TAC 1471 THEN
  FIRST_X_ASSUM(fun th -> if maychange_term (concl th) && not(is_forall(concl th))
                          then MP_TAC th else NO_TAC) THEN
  DISCH_TAC THEN MONOTONE_MAYCHANGE_TAC;;

let ZIT_END_TAC = REPEAT CONJ_TAC THEN (ZIT_MAYCHANGE_TAC ORELSE SI_DISCHARGE_TAC 1471);;

(*** steps 1 to 38: z_i and its norm check ***)

let ZIT_PART1_TAC =
  X86_STEPS_TAC SI44_ZIT_EXEC (1--6) THEN
  ZIT_SLICE_TAC `128 + 96 * i` `96` `s6:x86state` THEN
  ZIT_CALL_TAC "H_ETA" [`word_add sk (word (128 + 96 * i)):int64`; `rsp0:int64`; `pc:num`;
                        `\j. (skb:num->byte)((128 + 96 * i) + j)`] 7 THEN
  SIGN_UNPACK_POLY_OF_TAC `mld_polyeta_unpack_2` THEN
  X86_STEPS_TAC SI44_ZIT_EXEC (8--9) THEN
  ZIT_FCALL_TAC "H_NTT" [`read RDI s`;
    `mld_poly_of (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte)(128 + j))) i`] 10 THEN
  SIGN_NTT_POLY_OF_TAC THEN
  X86_STEPS_TAC SI44_ZIT_EXEC (11--12) THEN
  ZIT_CALL_TAC "H_PWM" [`rsp0:int64`; `pc:num`; ZIT_S1I; `cphat:num->int32`] 13 THEN
  X86_STEPS_TAC SI44_ZIT_EXEC (14--15) THEN
  ZIT_FCALL_TAC "H_INV" [`read RDI s`; ZIT_PW] 16 THEN
  ZIT_CALL_TAC "H_G1A" [`rsp0:int64`; `word_add rsp0 (word 736):int64`; `rhop:num`;
                        `kappa:num`; `i:num`; `pc:num`] 17 THEN
  ZIT_CALL_TAC "H_SQZ" [ZIT_S; `rsp0:int64`; `pc:num`] 18 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_shake256_stream]) THEN
  X86_STEPS_TAC SI44_ZIT_EXEC (19--21) THEN
  ZIT_CALL_TAC "H_UZ" [`word_add rsp0 (word 800):int64`; `rsp0:int64`; `pc:num`;
                       mk_comb(`mld_shake256_stream 66`,ZIT_M)] 22 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_poly_uniform_gamma1_17]) THEN
  SIGN_GAMMA_POLY_OF_TAC `mld_poly_uniform_gamma1_17` THEN
  ZIT_CALL_TAC "H_ZER" [`rsp0:int64`; `pc:num`] 23 THEN SI_RIP_NORM_TAC THEN
  X86_STEPS_TAC SI44_ZIT_EXEC (24--28) THEN
  ZIT_CALL_TAC "H_ADD" [`rsp0:int64`; `pc:num`; ZIT_YI; ZIT_CS1] 29 THEN
  X86_STEPS_TAC SI44_ZIT_EXEC (30--30) THEN ZIT_RCONST_TAC 30 0x1ad5 THEN
  X86_STEPS_TAC SI44_ZIT_EXEC (31--34) THEN
  ZIT_CALL_TAC "H_RED" [`rsp0:int64`; `pc:num`; list_mk_comb(`mld_poly_add`,[ZIT_CS1; ZIT_YI])] 35 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_sign_z]) THEN
  X86_STEPS_TAC SI44_ZIT_EXEC (36--37) THEN
  ZIT_CALL_TAC "H_CHK" [`rsp0:int64`; `pc:num`; ZIT_ZI] 38;;

(*** the packing of z_i and the back edge: steps 42 to 53 ***)

let ZIT_PART2_TAC =
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read RIP s = x`) (concl th)
                           then REWRITE_RULE[ASSUME `ok:bool`] th else th) THEN
  X86_STEPS_TAC SI44_ZIT_EXEC (42--44) THEN
  ZIT_CALL_TAC "H_ZP" [`word_add rsp0 (word 3296):int64`; `word_add sig (word (32 + 576 * i)):int64`;
                       `pc:num`; ZIT_ZI] 45 THEN
  X86_STEPS_TAC SI44_ZIT_EXEC (46--53) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP RIT_TEST4 (ASSUME `i < 4`)]) THEN
  ASM_CASES_TAC `i + 1 < 4` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(AP_TERM_TAC THEN ARITH_TAC THEN NO_TAC) THEN
  TRY(FIRST_ASSUM(ACCEPT_TAC o REWRITE_RULE[GSYM ADD_ASSOC]) THEN NO_TAC) THEN
  ZIT_END_TAC;;

let ZIT_FAIL_TAC =
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read RIP s = x`) (concl th)
                           then REWRITE_RULE[ASSUME `~ok`] th else th) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN ZIT_END_TAC;;

let ZIT_SETUP_TAC =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mcs = CONJ_PAIR th in
    MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
     [SI44_ETA30,"H_ETA"; SI44_PWM31,"H_PWM"; SI44_G1A_Z,"H_G1A";
      MP (SPEC_ALL SI44_SQZ_Z) mcs,"H_SQZ"; SI44_UZ_Z,"H_UZ";
      MP (SPEC_ALL SI44_ZER_Z) ms,"H_ZER"; SI44_ADD33,"H_ADD"; SI44_RED34,"H_RED";
      SI44_CHK35,"H_CHK"; SI44_ZP36,"H_ZP";
      MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_NTT";
      MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_INV"]) THEN
  CONCRETIZE_F_EVENTS_TAC ZIT_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `ok:bool`; `sig:int64`; `sk:int64`; `skb:num->byte`;
    `rsp0:int64`; `rhop:num`; `kappa:num`; `i:num`; `cphat:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES; fst SI44_ZIT_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SI_ALIGNED16_TAC [0; 0x320; 0xce0; 0x2500] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  SUBGOAL_THEN `i < 65536` ASSUME_TAC THENL [UNDISCH_TAC `i < 4` THEN ARITH_TAC; ALL_TAC];;

let SI44_ZIT = prove
 (SI44_ZIT_STMT,
  ZIT_SETUP_TAC THEN FULL_INIT_TAC THEN ZIT_PART1_TAC THEN
  X86_STEPS_TAC SI44_ZIT_EXEC (39--41) THEN RIT_DECIDE_TAC `ok:bool` THEN
  ASM_CASES_TAC `ok:bool` THENL [ZIT_PART2_TAC; ZIT_FAIL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The loop over z, for the first m polynomials, each of which passes the    *)
(* norm check (ZPRE), from after the NTT of the challenge, where the code    *)
(* sets up i = 0, as gcc's SIGN44_ZPRE: z_0 .. z_(m-1) packed into the       *)
(* signature after c~.                                                       *)
(* ------------------------------------------------------------------------- *)

let ZPRE_ZV = list_mk_comb(`mld_sign_z`, [SI44_S1H; `cphat:num->int32`; SI44_YK]);;
let ZPRE_ZI = mk_comb(ZPRE_ZV,`i:num`);;
let ZPRE_PACK = mk_comb(`mld_polyvec_pack 576 mld_polyz_pack_17`,
                        mk_comb(`mld_polyvec`,ZPRE_ZV));;

let SI44_ZPRE_STMT = parse_term(subst_tokens
  ["@MC@",image_mc; "@ZI@",string_of_term ZPRE_ZI; "@PACK@",string_of_term ZPRE_PACK;
   "@NEXT@",string_of_int SI44_ZNEXT]
 "!mf mc ea el ev.
     memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e m sig sk skb rsp0 rhop kappa cphat pc.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          aligned 32 rsp0 /\\ m <= 4 /\\
          (!i. i < m ==> mld_poly_chknorm (@ZI@) (word 130994) = word 0) /\\
          ALL (nonoverlapping (word_sub rsp0 (word 1471),11999))
              [(sig,2420); (sk,2560); (word pc,libmldsa_size);
               (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\\
          ALL (nonoverlapping (sig,2420))
              [(sk,2560); (word pc,libmldsa_size);
               (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
           (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + mldsa44_signature_internal_after_mldsa_poly_ntt_2) /\\
                read RSP s = rsp0 /\\
                read R12 s = word 0x0380200100000000 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes64 (word_add rsp0 (word 392))) s = word_add sig (word 39) /\\
                read (memory :> bytes64 (word_add rsp0 (word 96))) s = word_add sk (word 128) /\\
                read (memory :> bytes64 (word_add rsp0 (word 128))) s = word_add rsp0 (word 736) /\\
                read (memory :> bytes16 (word_add rsp0 (word 136))) s = word kappa /\\
                read (memory :> bytes (word_add rsp0 (word 736),64)) s = rhop /\\
                (!k. k < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (9472 + 4 * k)))) s =
                                 cphat k) /\\
                (!k. k < 2560 ==> read (memory :> bytes8 (word_add sk (word k))) s = skb k) /\\
                read events s = e)
           (\\s. read RIP s =
                (if m < 4 then word (pc + mldsa44_signature_internal_join11)
                 else word (pc + @NEXT@)) /\\
                read RSP s = rsp0 /\\ read R12 s = word 0x0380200100000000 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read R13 s = word m /\\ read RCX s = word (2 + 96 * m) /\\
                read R10 s = word_add sig (word (39 + 576 * m)) /\\
                (!t. t < 576 * m ==> read (memory :> bytes8 (word_add sig (word (32 + t)))) s =
                                     @PACK@ t) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events m sig sk rsp0 mf mc pc /\\
                   memaccess_inbounds e2
                    [sig,2420; sk,2560; word_sub rsp0 (word 1471),11999;
                     word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa44_signature_internal_consts),32;
                     word(pc + mldsa_poly_ntt_consts),256;
                     word(pc + mldsa_poly_invntt_tomont_consts),448]
                    [sig,2420; word_sub rsp0 (word 1471),11999]))
           (MAYCHANGE [RSP; RBX; R10; R12; R13; R14; R15] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(word_sub rsp0 (word 296),296);
                       memory :> bytes(word_add rsp0 (word 16),8);
                       memory :> bytes(word_add rsp0 (word 152),8);
                       memory :> bytes(word_add rsp0 (word 160),208);
                       memory :> bytes(word_add rsp0 (word 408),8);
                       memory :> bytes(word_add rsp0 (word 416),66);
                       memory :> bytes(word_add rsp0 (word 800),1024);
                       memory :> bytes(word_add rsp0 (word 2592),680);
                       memory :> bytes(word_add rsp0 (word 3296),1024);
                       memory :> bytes(word_add sig (word 32),2304)])");;

let SI44_ZPRE_EXEC = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
  [(layout "mldsa44_signature_internal_after_mldsa_poly_ntt_2", SI44_ZNEXT);
   layout_range "plt_memset"; layout_range "plt_memcpy"];;

let ZPRE_INV = parse_term(subst_tokens ["@PACK@",string_of_term ZPRE_PACK]
 "\\i s. read RSP s = rsp0 /\\ read R12 s = word 0x0380200100000000 /\\
       (read DF s <=> false) /\\
       read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
       read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
       read (memory :> bytes(ea,el)) s = ev /\\
       read R13 s = word i /\\ read RCX s = word (2 + 96 * i) /\\
       read R10 s = word_add sig (word (39 + 576 * i)) /\\
       read (memory :> bytes64 (word_add rsp0 (word 392))) s = word_add sig (word 39) /\\
       read (memory :> bytes64 (word_add rsp0 (word 96))) s = word_add sk (word 128) /\\
       read (memory :> bytes64 (word_add rsp0 (word 128))) s = word_add rsp0 (word 736) /\\
       read (memory :> bytes16 (word_add rsp0 (word 136))) s = word kappa /\\
       read (memory :> bytes (word_add rsp0 (word 736),64)) s = rhop /\\
       (!k. k < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (9472 + 4 * k)))) s =
                        cphat k) /\\
       (!k. k < 2560 ==> read (memory :> bytes8 (word_add sk (word k))) s = skb k) /\\
       (!t. t < 576 * i ==> read (memory :> bytes8 (word_add sig (word (32 + t)))) s =
                            @PACK@ t)");;

let ZPRE_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `i < 4` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    can (term_match [] `!i. i < m ==> P i`) (concl th) && is_forall(concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FULL_INIT_TAC THEN
  REMOVE_THEN "H_ZIT" (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (VM_MC,SI44_ZPRE_EXEC,0x0,VM_MC,th)
      [`e:(uarch_event)list`; `T`; `sig:int64`; `sk:int64`; `skb:num->byte`; `rsp0:int64`;
       `rhop:num`; `kappa:num`; `i:num`; `cphat:num->int32`; `pc:num`] 1 THENL
     [REPEAT CONJ_TAC THEN TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
      VM_PRE_TAC [`sig:int64`; `sk:int64`; `rsp0:int64`; `i:num`; `mf:int64`; `mc:int64`; `pc:num`];
      LABEL_TAC "H_ZIT" th]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP RPRE_PC (CONJ (ASSUME `i < m`) (ASSUME `m <= 4`))]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC(ISPECL [`mld_polyz_pack_17`; `576`] SIGN_PACK_JOIN) THEN
      ASM_REWRITE_TAC[SIGN_POLYZ_PACK_17_LOCAL] THEN NO_TAC) THEN
  TRY(FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
  SIGN_LOOP_DISCHARGE_TAC;;

let SI44_ZPRE = prove
 (SI44_ZPRE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SI_ASSUME_CALLEE_TAILED_TAC (MP (SPEC_ALL SI44_ZIT) th) "H_ZIT") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(m:num) (sig:int64) (sk:int64) (rsp0:int64) (mf:int64) (mc:int64) (pc:num).
     APPEND (f_ev_back m sig sk rsp0 mf mc pc)
      (APPEND (ENUMERATEL m (\i. f_ev_zit sig sk rsp0 mf mc pc i))
              (f_ev_front sig sk rsp0 mf mc pc))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `m:num`; `sig:int64`; `sk:int64`; `skb:num->byte`;
    `rsp0:int64`; `rhop:num`; `kappa:num`; `cphat:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst SI44_ZPRE_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `0 < m` THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `m:num`
     `pc + mldsa44_signature_internal_join11`
     (mk_comb(mk_comb(mk_comb(`COND:bool->num->num->num`,`m < 4`),
        `pc + mldsa44_signature_internal_join11`),
        mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral SI44_ZNEXT)))
     ZPRE_INV THEN
    REPEAT CONJ_TAC THENL
     [SIMPLE_ARITH_TAC;
      REWRITE_TAC[CONJUNCT1 LT; MULT_CLAUSES; ADD_CLAUSES; LE_0] THEN
      FULL_INIT_TAC THEN X86_STEPS_TAC SI44_ZPRE_EXEC (1--3) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN
      SI_DISCHARGE_TAC 1471;
      ZPRE_BODY_TAC;
      REWRITE_TAC[] THEN FULL_INIT_TAC THEN SIGN_PC_COND_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      SIGN_BETA_ALL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC];
    SUBGOAL_THEN `m = 0` SUBST_ALL_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN X86_STEPS_TAC SI44_ZPRE_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ARITH; MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    REWRITE_TAC[ENUMERATEL; APPEND; APPEND_NIL] THEN SI_DISCHARGE_TAC 1471]);;

(* ------------------------------------------------------------------------- *)
(* Column j of the product of the matrix with y (YCOL j, j = 0 .. 3), from   *)
(* join4 to join3: y_j sampled (absorbing rho'' || kappa + j, squeezing,     *)
(* unpacking at rsp0 + 0x320, zeroing) and transformed, then for each row r  *)
(* the entry A_rj sampled by mldsa_poly_uniform from rho || j || r at rsp0 + *)
(* 0xa0 and multiplied by it: for j = 0 into row r of w at rsp0 + 0x1500 +   *)
(* 1024 r, for j > 0 into the scratch polynomial at rsp0 + 0x10e0 and added  *)
(* to row r. Row r is then mld_lazy_acc rho r YHAT j, YHAT being y in the    *)
(* NTT domain. For j > 0 the code also loads the constants of the reduction  *)
(* that follows the loop into XMM5 and XMM6. The lemma is made for each j,   *)
(* with j a numeral, from one generator.                                     *)
(* ------------------------------------------------------------------------- *)

let SI_SEED16 = prove
 (`!a:int64 r i j s:x86state.
        read (memory :> bytes(a,32)) s = r /\
        read (memory :> bytes16(word_add a (word 32))) s = word (j + 256 * i) /\
        j + 256 * i < 65536
        ==> read (memory :> bytes(a,34)) s = mld_matrix_seed r i j`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mld_matrix_seed; ARITH_RULE `34 = 32 + 2`;
              READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[CONJUNCT1 MLD_BYTES2] THEN ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT]);;

let SI44_YHAT = `mld_polyvec_map mld_poly_ntt (mld_sign_y mld_poly_uniform_gamma1_17 rhop kappa)`;;

let ycol_row r n =
  Printf.sprintf
   "(!k. k < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4 * k)))) s =
                     mld_lazy_acc rho %d (%s) %d k)"
   (5376 + 1024 * r) r (string_of_term SI44_YHAT) n;;

let ycol_rows n = String.concat " /\\\n " (map (fun r -> ycol_row r n) [0;1;2;3]);;

let YCOL_STMT j = parse_term(subst_tokens
  ["@MC@",image_mc;
   "@PRE@",(if j = 0 then "" else ycol_rows (j - 1) ^ " /\\");
   "@POST@",ycol_rows j;
   "@XMM@",
     "read XMM5 s = word 0x00400000004000000040000000400000 /\\
      read XMM6 s = word 0xff801fffff801fffff801fffff801fff /\\";
   "@J@",string_of_int j]
 "!mf mc ea el ev.
     memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e rsp0 rho rhop kappa pc.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          aligned 32 rsp0 /\\ mld_matrix_terminates 4 4 rho /\\
          ALL (nonoverlapping (word_sub rsp0 (word 1471),11999))
              [(word pc,libmldsa_size);
               (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
           (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + mldsa44_signature_internal_join4) /\\
                read RSP s = rsp0 /\\ read R14 s = word @J@ /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes64 (word_add rsp0 (word 128))) s = word_add rsp0 (word 736) /\\
                read (memory :> bytes16 (word_add rsp0 (word 136))) s = word kappa /\\
                read (memory :> bytes (word_add rsp0 (word 736),64)) s = rhop /\\
                read (memory :> bytes (word_add rsp0 (word 160),32)) s = rho /\\
                @PRE@
                read events s = e)
           (\\s. read RIP s = word (pc + mldsa44_signature_internal_join3) /\\
                read RSP s = rsp0 /\\ read R14 s = word @J@ /\\
                read R12 s = word 0x0380200100000000 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes64 (word_add rsp0 (word 128))) s = word_add rsp0 (word 736) /\\
                read (memory :> bytes16 (word_add rsp0 (word 136))) s = word kappa /\\
                read (memory :> bytes (word_add rsp0 (word 736),64)) s = rhop /\\
                read (memory :> bytes (word_add rsp0 (word 160),32)) s = rho /\\
                @XMM@
                @POST@ /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events rsp0 rho mf mc pc /\\
                   memaccess_inbounds e2
                    [word_sub rsp0 (word 1471),11999;
                     word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa44_signature_internal_consts),32;
                     word(pc + mldsa_poly_ntt_consts),256]
                    [word_sub rsp0 (word 1471),11999]))
           (MAYCHANGE [RSP; RBX; R12; R13; R14; R15] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(word_sub rsp0 (word 1471),1471);
                       memory :> bytes(word_add rsp0 (word 16),8);
                       memory :> bytes(word_add rsp0 (word 192),2);
                       memory :> bytes(word_add rsp0 (word 800),1024);
                       memory :> bytes(word_add rsp0 (word 1824),208);
                       memory :> bytes(word_add rsp0 (word 2592),66);
                       memory :> bytes(word_add rsp0 (word 4320),1024);
                       memory :> bytes(word_add rsp0 (word 5376),4096);
                       memory :> bytes(word_add rsp0 (word 9472),680)])");;

let SI44_YCOL_EXEC = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
  [(layout "mldsa44_signature_internal_join4", layout "mldsa44_signature_internal_join10");
   layout_range "plt_memset"; layout_range "plt_memcpy"];;

let YCOL_ALLOWED = [`rsp0:int64`; `rho:num`; `mf:int64`; `mc:int64`; `pc:num`];;

let YCOL_CALL_TAC name ilist n =
  REMOVE_THEN name (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (VM_MC,SI44_YCOL_EXEC,0x0,VM_MC,th)
      (`e:(uarch_event)list`::ilist) n THENL
     [REPEAT CONJ_TAC THEN
      TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
      TRY(REWRITE_TAC[GSYM ADD_ASSOC] THEN FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
      TRY(SI_BOUND_TAC THEN NO_TAC) THEN
      VM_PRE_TAC YCOL_ALLOWED;
      LABEL_TAC name th]);;

let YCOL_FCALL_TAC name ilist n =
  YCOL_CALL_TAC name
   (ilist @ [`pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]) n THEN
  RSP_NORM_TAC THEN EXPAND_CALLEE_MEMACCESS_TAC;;

let YCOL_Y = `mld_sign_y mld_poly_uniform_gamma1_17 rhop kappa`;;

(*** y_j and its NTT: steps 1 to 15 ***)

let YCOL_HEAD_TAC j =
  let jt = mk_small_numeral j in
  let m = subst [jt,`j:num`] `rhop + 2 EXP 512 * val(word(kappa + j):int16)` in
  YCOL_CALL_TAC "H_G1A" [`rsp0:int64`; `word_add rsp0 (word 736):int64`; `rhop:num`;
                         `kappa:num`; jt; `pc:num`] 1 THEN
  YCOL_CALL_TAC "H_SQZ" [mk_comb(`mld_keccak_absorb_once 136 0x1F 66`,m); `rsp0:int64`; `pc:num`] 2 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_shake256_stream]) THEN
  X86_STEPS_TAC SI44_YCOL_EXEC (3--5) THEN
  YCOL_CALL_TAC "H_UZ" [`word_add rsp0 (word 800):int64`; `rsp0:int64`; `pc:num`;
                        mk_comb(`mld_shake256_stream 66`,m)] 6 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_poly_uniform_gamma1_17]) THEN
  SIGN_GAMMA_POLY_OF_TAC `mld_poly_uniform_gamma1_17` THEN
  YCOL_CALL_TAC "H_ZER" [`rsp0:int64`; `pc:num`] 7 THEN SI_RIP_NORM_TAC THEN
  X86_STEPS_TAC SI44_YCOL_EXEC (8--10) THEN
  YCOL_FCALL_TAC "H_NTT" [`read RDI s`; mk_comb(mk_comb(`mld_poly_of`,YCOL_Y),jt)] 11 THEN
  SIGN_NTT_POLY_OF_TAC THEN
  X86_STEPS_TAC SI44_YCOL_EXEC (12--12) THEN
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read R14 s = x`) (concl th)
                           then CONV_RULE(RAND_CONV WORD_REDUCE_CONV) th else th) THEN
  X86_STEPS_TAC SI44_YCOL_EXEC (13--15);;

(*** row r of a column: the seed rho || j || r, the sampling of the entry   ***)
(*** (the CALL at step n), its product with y_j and, for j > 0, the sum     ***)

let YCOL_SEED_TAC j r st =
  if j = 0 then
    MP_TAC(SPECL [`word_add rsp0 (word 160):int64`; `rho:num`; mk_small_numeral r; `0`; st]
                 SI_SEED16) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[WORD_RULE `word_add (word_add (x:int64) (word 160)) (word 32) =
                           word_add x (word 192)`] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC
  else
    RULE_ASSUM_TAC(fun th ->
      if can (term_match [] `read (memory :> bytes8 a) s = x`) (concl th)
      then CONV_RULE(RAND_CONV(DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV)) th
      else th) THEN
    MP_TAC(SPECL [`word_add rsp0 (word 160):int64`; `rho:num`; mk_small_numeral r;
                  mk_small_numeral j; st] LAZY_SEED) THEN
    REWRITE_TAC[WORD_RULE `word_add (word_add (x:int64) (word 160)) (word 32) =
                           word_add x (word 192)`;
                WORD_RULE `word_add (word_add (x:int64) (word 160)) (word 33) =
                           word_add x (word 193)`] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC;;

let YCOL_PU_TAC j r n =
  let jt = mk_small_numeral j and rt = mk_small_numeral r in
  let sd = list_mk_comb(`mld_matrix_seed`,[`rho:num`; rt; jt]) in
  let st = mk_var("s"^string_of_int (n - 1),`:x86state`) in
  YCOL_SEED_TAC j r st THEN
  MLD_LAZY_TERM_TAC (mk_comb(`mld_rej_uniform_terminates`,mk_comb(`mld_shake128_stream 34`,sd))) THEN
  YCOL_FCALL_TAC "H_PU" [`read RDI s`; `read RSI s`; sd] n THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_matrix_entry]);;

let YCOL_TAC j =
  let jt = mk_small_numeral j in
  let yh = mk_comb(mk_comb(`mld_poly_of`,SI44_YHAT),jt) in
  let entry r = list_mk_comb(`mld_matrix_entry`,[`rho:num`; mk_small_numeral r; jt]) in
  let pwm r = list_mk_comb(`mld_poly_pointwise_montgomery`,[entry r; yh]) in
  let acc r n = list_mk_comb(`mld_lazy_acc rho`,[mk_small_numeral r; SI44_YHAT; mk_small_numeral n]) in
  let acc_eq r =
    if j = 0 then GSYM(CONJUNCT1 mld_lazy_acc)
    else SYM(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
              (SPECL [`rho:num`; mk_small_numeral r; SI44_YHAT; mk_small_numeral (j - 1)]
                     MLD_LAZY_ACC_ADD1)) in
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mcs = CONJ_PAIR th in
    MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
     ([SI44_G1A_Y,"H_G1A"; MP (SPEC_ALL SI44_SQZ_Y) mcs,"H_SQZ"; SI44_UZ_Y,"H_UZ";
       MP (SPEC_ALL SI44_ZER_Y) ms,"H_ZER";
       MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_NTT";
       MP (SPEC_ALL MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th,
       "H_PU"] @
      (if j = 0 then [SI44_PWM10,"H_PWM0"; SI44_PWM11,"H_PWM1"; SI44_PWM12,"H_PWM2";
                      SI44_PWM13,"H_PWM3"]
       else [SI44_PWM2,"H_PWM0"; SI44_PWM4,"H_PWM1"; SI44_PWM6,"H_PWM2"; SI44_PWM8,"H_PWM3";
             SI44_ADD3,"H_ADD0"; SI44_ADD5,"H_ADD1"; SI44_ADD7,"H_ADD2"; SI44_ADD9,"H_ADD3"]))) THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (rho:num) (mf:int64) (mc:int64) (pc:num).
      f_ev_col rsp0 rho mf mc pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `rho:num`; `rhop:num`;
                       `kappa:num`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst SI44_YCOL_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mld_matrix_terminates]) THEN
  SI_ALIGNED16_TAC [0; 0x320; 0x10e0; 0x1500; 0x1900; 0x1d00; 0x2100] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  FULL_INIT_TAC THEN YCOL_HEAD_TAC j THEN
  (if j = 0 then
    MAP_EVERY (fun r ->
      let n = 16 + 8 * r in
      X86_STEPS_TAC SI44_YCOL_EXEC (n--(n+3)) THEN YCOL_PU_TAC j r (n+4) THEN
      (if r = 3 then
         X86_STEPS_TAC SI44_YCOL_EXEC ((n+5)--(n+5)) THEN RIT_RCONST_TAC (n+5) 0xc6d THEN
         X86_STEPS_TAC SI44_YCOL_EXEC ((n+6)--(n+8)) THEN
         YCOL_CALL_TAC ("H_PWM"^string_of_int r) [`rsp0:int64`; `pc:num`; entry r; yh] (n+9)
       else
         X86_STEPS_TAC SI44_YCOL_EXEC ((n+5)--(n+6)) THEN
         YCOL_CALL_TAC ("H_PWM"^string_of_int r) [`rsp0:int64`; `pc:num`; entry r; yh] (n+7)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[acc_eq r])) [0;1;2;3] THEN
    X86_STEPS_TAC SI44_YCOL_EXEC (50--50)
   else
    MAP_EVERY (fun r ->
      let n = if r = 0 then 16 else 17 + 12 * r in
      let ncall = if r = 0 then 21 else n + 4 in
      X86_STEPS_TAC SI44_YCOL_EXEC (n--ncall) THEN YCOL_PU_TAC j r (ncall+1) THEN
      X86_STEPS_TAC SI44_YCOL_EXEC ((ncall+2)--(ncall+3)) THEN
      YCOL_CALL_TAC ("H_PWM"^string_of_int r) [`rsp0:int64`; `pc:num`; entry r; yh] (ncall+4) THEN
      X86_STEPS_TAC SI44_YCOL_EXEC ((ncall+5)--(ncall+5)) THEN
      (if r = 3 then RIT_RCONST_TAC (ncall+5) 0x9ce THEN
                     X86_STEPS_TAC SI44_YCOL_EXEC ((ncall+6)--(ncall+8))
       else X86_STEPS_TAC SI44_YCOL_EXEC ((ncall+6)--(ncall+6))) THEN
      YCOL_CALL_TAC ("H_ADD"^string_of_int r) [`rsp0:int64`; `pc:num`; pwm r; acc r (j - 1)]
        (if r = 3 then ncall+9 else ncall+7) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[acc_eq r])) [0;1;2;3] THEN
    X86_STEPS_TAC SI44_YCOL_EXEC (67--67)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[XMM5; XMM6; READ_COMPONENT_COMPOSE; READ_ZEROTOP_128] THEN
      ASM_REWRITE_TAC[VM_ZX_JOIN] THEN CONV_TAC WORD_REDUCE_CONV THEN NO_TAC) THEN
  RIT_END_TAC;;

let SI44_YCOL0 = prove(YCOL_STMT 0, YCOL_TAC 0);;
let SI44_YCOL1 = prove(YCOL_STMT 1, YCOL_TAC 1);;
let SI44_YCOL2 = prove(YCOL_STMT 2, YCOL_TAC 2);;
let SI44_YCOL3 = prove(YCOL_STMT 3, YCOL_TAC 3);;

(* ------------------------------------------------------------------------- *)
(* Vectors of four polynomials in memory, row by row and as a whole.         *)
(* ------------------------------------------------------------------------- *)

let SI_JOIN_VEC32 = prove
 (`!(B:int64) off (V:num->int32) (s:x86state).
        (!r k. r < 4 /\ k < 256
               ==> read (memory :> bytes32 (word_add B (word ((off + 1024 * r) + 4 * k)))) s =
                   mld_poly_of V r k)
        ==> !i. i < 1024 ==> read (memory :> bytes32 (word_add B (word (off + 4 * i)))) s = V i`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`i DIV 256`; `i MOD 256`]) THEN
  REWRITE_TAC[mld_poly_of] THEN
  MP_TAC(SPECL [`i:num`; `256`] DIVISION) THEN CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_EQ_CONV)) THEN
  REWRITE_TAC[] THEN
  MAP_EVERY ABBREV_TAC [`q = i DIV 256`; `t = i MOD 256`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `q < 4 /\ (off + 1024 * q) + 4 * t = off + 4 * i /\ 256 * q + t = i`
   (fun th -> REWRITE_TAC[th] THEN ASM_REWRITE_TAC[]) THEN
  MAP_EVERY UNDISCH_TAC [`i = q * 256 + t`; `t < 256`; `i < 1024`] THEN ARITH_TAC);;

let SI_JOIN_VEC8 = prove
 (`!(B:int64) off (P:num->byte) (s:x86state).
        (!r j. r < 4 /\ j < 192
               ==> read (memory :> bytes8 (word_add B (word ((off + 192 * r) + j)))) s =
                   P (192 * r + j))
        ==> !t. t < 768 ==> read (memory :> bytes8 (word_add B (word (off + t)))) s = P t`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`t DIV 192`; `t MOD 192`]) THEN
  MP_TAC(SPECL [`t:num`; `192`] DIVISION) THEN CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_EQ_CONV)) THEN
  REWRITE_TAC[] THEN
  MAP_EVERY ABBREV_TAC [`q = t DIV 192`; `u = t MOD 192`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `q < 4 /\ (off + 192 * q) + u = off + t /\ 192 * q + u = t`
   (fun th -> REWRITE_TAC[th] THEN ASM_REWRITE_TAC[]) THEN
  MAP_EVERY UNDISCH_TAC [`t = q * 192 + u`; `u < 192`; `t < 768`] THEN ARITH_TAC);;

let SI_SLICE_VEC32 = prove
 (`!(B:int64) off (V:num->int32) (s:x86state) r.
        (!i. i < 1024 ==> read (memory :> bytes32 (word_add B (word (off + 4 * i)))) s = V i) /\
        r < 4
        ==> !k. k < 256
                ==> read (memory :> bytes32 (word_add B (word ((off + 1024 * r) + 4 * k)))) s =
                    mld_poly_of V r k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_poly_of] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `256 * r + k`) THEN
  REWRITE_TAC[ARITH_RULE `off + 4 * (256 * r + k) = (off + 1024 * r) + 4 * k`] THEN
  DISCH_THEN MATCH_MP_TAC THEN MAP_EVERY UNDISCH_TAC [`r < 4`; `k < 256`] THEN ARITH_TAC);;

let SI_MAP_POLY_OF = prove
 (`!(f:(num->int32)->num->int32) x r (B:int64) d (s:x86state).
     (!k. k < 256 ==> read (memory :> bytes32 (word_add B (word (d + 4 * k)))) s =
                      f (mld_poly_of x r) k)
     ==> (!k. k < 256 ==> read (memory :> bytes32 (word_add B (word (d + 4 * k)))) s =
                          mld_poly_of (mld_polyvec_map f x) r k)`,
  SIMP_TAC[MLD_POLY_OF_POLYVEC_MAP]);;

let SI_POLYVEC_POLY_OF = prove
 (`!(F:num->num->int32) r (B:int64) d (s:x86state).
     (!k. k < 256 ==> read (memory :> bytes32 (word_add B (word (d + 4 * k)))) s = F r k)
     ==> (!k. k < 256 ==> read (memory :> bytes32 (word_add B (word (d + 4 * k)))) s =
                          mld_poly_of (mld_polyvec F) r k)`,
  SIMP_TAC[MLD_POLY_OF_POLYVEC]);;

(* the facts for rows 0 .. 3 at B + off + 1024 r as one fact over r *)
let SI_ROWS4_TAC b off st (pat:term) =
  let gl = subst [b,`B:int64`; mk_small_numeral off,`off:num`; st,`s:x86state`] pat in
  SUBGOAL_THEN gl ASSUME_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN FIRST_ASSUM ACCEPT_TAC);
    ALL_TAC];;

(* the fact of the form f (mld_poly_of x r) k after a region lemma, as row r
   of mld_polyvec_map f x *)
let SI_MAP_POLY_OF_TAC f =
  let pat = subst [f,`f:(num->int32)->num->int32`]
   `!k. k < 256
        ==> read (memory :> bytes32 (word_add B (word (d + 4 * k)))) s =
            (f:(num->int32)->num->int32) (mld_poly_of x r) k` in
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP SI_MAP_POLY_OF o
    check (fun th -> can (term_match [] pat) (concl th)));;

(* ------------------------------------------------------------------------- *)
(* After the product with the matrix (HPOST), from join10 to after the NTT  *)
(* of the challenge: the seed buffer zeroed, the rows of w reduced (XMM5 and *)
(* XMM6 as YCOL 3 left them), transformed back and made nonnegative, which   *)
(* MLD_LAZY_SIGN_W turns into w = A y of the model; w decomposed in place    *)
(* into w0, w1 packed at rsp0 + 0x720, c~ = H(mu || w1) at rsp0 + 0x200      *)
(* with mld_H44 (stack arguments NULL and 0), the challenge at rsp0 + 0x2500 *)
(* and its NTT.                                                              *)
(* ------------------------------------------------------------------------- *)

let SI44_A = `mld_polyvec_matrix_expand 4 rho`;;
let SI44_W = list_mk_comb(`mld_sign_w 4`,[SI44_A; YCOL_Y]);;
let SI44_W1 = mk_comb(`mld_sign_w1 (mld_polyw1_pack_88 o mld_poly_decompose_hi_88) 192`,SI44_W);;
let SI44_W1NUM = mk_comb(`num_of_bytelist`,
  list_mk_comb(`list_of_seq:(num->byte)->num->(byte)list`,[SI44_W1; `768`]));;
let SI44_CT = mk_comb(`mld_sign_ctilde 4 192 mu`,SI44_W1);;

let SI44_HPOST_STMT = parse_term(subst_tokens
  ["@MC@",image_mc; "@PRE@",ycol_rows 3; "@W@",string_of_term SI44_W;
   "@W1@",string_of_term SI44_W1; "@CT@",string_of_term SI44_CT]
 "!mf mc ea el ev.
     memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e rsp0 rho rhop kappa mu C pc.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          aligned 32 rsp0 /\\ mld_matrix_terminates 4 4 rho /\\
          num_of_bytelist(list_of_seq (@CT@) 32) = C /\\
          mld_poly_challenge_terminates 39 32 C /\\
          ALL (nonoverlapping (word_sub rsp0 (word 1471),11999))
              [(word pc,libmldsa_size);
               (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
           (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + mldsa44_signature_internal_join10) /\\
                read RSP s = rsp0 /\\ read R12 s = word 0x0380200100000000 /\\
                read XMM5 s = word 0x00400000004000000040000000400000 /\\
                read XMM6 s = word 0xff801fffff801fffff801fffff801fff /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes (word_add rsp0 (word 672),64)) s = mu /\\
                @PRE@ /\\
                read events s = e)
           (\\s. read RIP s = word (pc + mldsa44_signature_internal_after_mldsa_poly_ntt_2) /\\
                read RSP s = rsp0 /\\ read R12 s = word 0x0380200100000000 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                (!i. i < 1024 ==> read (memory :> bytes32 (word_add rsp0 (word (5376 + 4 * i)))) s =
                                  mld_polyvec_map mld_poly_decompose_lo_88 (@W@) i) /\\
                (!j. j < 768 ==> read (memory :> bytes8 (word_add rsp0 (word (1824 + j)))) s =
                                 (@W1@) j) /\\
                read (memory :> bytes (word_add rsp0 (word 512),32)) s = C /\\
                (!k. k < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (9472 + 4 * k)))) s =
                                 mld_poly_ntt (mld_poly_challenge 39 32 C) k) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events rsp0 C mf mc pc /\\
                   memaccess_inbounds e2
                    [word_sub rsp0 (word 1471),11999;
                     word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa44_poly_challenge_consts),64;
                     word(pc + mldsa_poly_ntt_consts),256;
                     word(pc + mldsa_poly_invntt_tomont_consts),448]
                    [word_sub rsp0 (word 1471),11999]))
           (MAYCHANGE [RSP; RBX; R12; R13; R14; R15] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(word_sub rsp0 (word 1471),1471);
                       memory :> bytes(word_add rsp0 (word 160),64);
                       memory :> bytes(word_add rsp0 (word 512),32);
                       memory :> bytes(word_add rsp0 (word 800),1024);
                       memory :> bytes(word_add rsp0 (word 1824),768);
                       memory :> bytes(word_add rsp0 (word 5376),4096);
                       memory :> bytes(word_add rsp0 (word 9472),1024)])");;

let SI44_HPOST_EXEC = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
  [(layout "mldsa44_signature_internal_join10", layout "mldsa44_signature_internal_after_mldsa_poly_ntt_2")];;

let HPOST_ALLOWED = [`rsp0:int64`; `C:num`; `mf:int64`; `mc:int64`; `pc:num`];;

let HPOST_CALL_TAC name ilist n =
  REMOVE_THEN name (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (VM_MC,SI44_HPOST_EXEC,0x0,VM_MC,th)
      (`e:(uarch_event)list`::ilist) n THENL
     [REPEAT CONJ_TAC THEN
      TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
      TRY(REWRITE_TAC[GSYM ADD_ASSOC] THEN FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
      TRY(SI_BOUND_TAC THEN NO_TAC) THEN
      VM_PRE_TAC HPOST_ALLOWED;
      LABEL_TAC name th]);;

let HPOST_FCALL_TAC name ilist n =
  HPOST_CALL_TAC name
   (ilist @ [`pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]) n THEN
  RSP_NORM_TAC THEN EXPAND_CALLEE_MEMACCESS_TAC;;

let HPOST_V = `mld_polyvec (\i. mld_lazy_acc rho i
                (mld_polyvec_map mld_poly_ntt (mld_sign_y mld_poly_uniform_gamma1_17 rhop kappa)) 3)`;;
let HPOST_RV = mk_comb(`mld_polyvec_map mld_poly_reduce`,HPOST_V);;
let HPOST_IV = mk_comb(`mld_polyvec_map mld_poly_invntt_tomont`,HPOST_RV);;
let HPOST_CV = mk_comb(`mld_polyvec_map mld_poly_caddq`,HPOST_IV);;
let HPOST_ROW v r = mk_comb(mk_comb(`mld_poly_of`,v),mk_small_numeral r);;

(* row r of the lazy sums as row r of the vector HPOST_V *)
let HPOST_V_TAC r =
  let off = 5376 + 1024 * r in
  FIRST_X_ASSUM(fun th ->
    let pat = subst [mk_small_numeral off,`d:num`; mk_small_numeral r,`r:num`]
     `!k. k < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (d + 4 * k)))) s =
                      mld_lazy_acc rho r YH 3 k` in
    if can (term_match [] pat) (concl th) then
      ASSUME_TAC(MATCH_MP (BETA_RULE(ISPECL
        [`\i. mld_lazy_acc rho i (mld_polyvec_map mld_poly_ntt
                (mld_sign_y mld_poly_uniform_gamma1_17 rhop kappa)) 3`;
         mk_small_numeral r] SI_POLYVEC_POLY_OF)) th)
    else NO_TAC);;

let HPOST_LAZY_W_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
   `!i. i < 1024
        ==> read (memory :> bytes32 (word_add B (word (d + 4 * i)))) s =
            mld_polyvec_map mld_poly_caddq x i`) (concl th))) THEN
  MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
   (SPECL [`4`; `4`; `rho:num`; YCOL_Y] MLD_LAZY_SIGN_W)) THEN
  REWRITE_TAC[MLD_LAZY_SIGN_Y_BOUND; ASSUME `mld_matrix_terminates 4 4 rho`] THEN
  DISCH_THEN(fun th -> SIMP_TAC[th]) THEN DISCH_TAC;;

let HPOST_YVEC = prove
 (mk_eq(list_mk_comb(`mld_polyvec_matrix_yvec_lazy 4 rho`,[YCOL_Y]),HPOST_IV),
  REWRITE_TAC[mld_polyvec_matrix_yvec_lazy] THEN CONV_TAC NUM_REDUCE_CONV);;

let HPOST_ROWS_PAT32 =
 `!r. r < 4 ==> !k. k < 256
      ==> read (memory :> bytes32 (word_add B (word ((off + 1024 * r) + 4 * k)))) s =
          mld_poly_of V r k`;;

(*** the rows of w: steps 1 to 43 ***)

let HPOST_PART1_TAC =
  X86_STEPS_TAC SI44_HPOST_EXEC (1--8) THEN
  MAP_EVERY HPOST_V_TAC [0;1;2;3] THEN
  MAP_EVERY (fun r ->
    (if r > 0 then X86_STEPS_TAC SI44_HPOST_EXEC ((6 + 3 * r + 1)--(6 + 3 * r + 2)) else ALL_TAC) THEN
    HPOST_CALL_TAC ("H_RED"^string_of_int r) [`rsp0:int64`; `pc:num`; HPOST_ROW HPOST_V r]
      (9 + 3 * r) THEN
    SI_MAP_POLY_OF_TAC `mld_poly_reduce`) [0;1;2;3] THEN
  MAP_EVERY (fun r ->
    X86_STEPS_TAC SI44_HPOST_EXEC ((19 + 3 * r)--(20 + 3 * r)) THEN
    HPOST_FCALL_TAC "H_INV" [`read RDI s`; HPOST_ROW HPOST_RV r] (21 + 3 * r) THEN
    SI_MAP_POLY_OF_TAC `mld_poly_invntt_tomont`) [0;1;2;3] THEN
  X86_STEPS_TAC SI44_HPOST_EXEC (31--32) THEN
  HPOST_CALL_TAC "H_CQ0" [`rsp0:int64`; `pc:num`; HPOST_ROW HPOST_IV 0] 33 THEN
  SI_MAP_POLY_OF_TAC `mld_poly_caddq` THEN
  X86_STEPS_TAC SI44_HPOST_EXEC (34--36) THEN
  HPOST_CALL_TAC "H_CQ1" [`rsp0:int64`; `pc:num`; HPOST_ROW HPOST_IV 1] 37 THEN
  SI_MAP_POLY_OF_TAC `mld_poly_caddq` THEN
  X86_STEPS_TAC SI44_HPOST_EXEC (38--39) THEN
  HPOST_CALL_TAC "H_CQ2" [`rsp0:int64`; `pc:num`; HPOST_ROW HPOST_IV 2] 40 THEN
  SI_MAP_POLY_OF_TAC `mld_poly_caddq` THEN
  X86_STEPS_TAC SI44_HPOST_EXEC (41--42) THEN
  HPOST_CALL_TAC "H_CQ3" [`rsp0:int64`; `pc:num`; HPOST_ROW HPOST_IV 3] 43 THEN
  SI_MAP_POLY_OF_TAC `mld_poly_caddq`;;

(*** w as w = A y, its decomposition and the packing of w1: steps 44 to 71 ***)

let HPOST_PART2_TAC =
  SI_ROWS4_TAC `rsp0:int64` 5376 `s43:x86state` (subst [HPOST_CV,`V:num->int32`] HPOST_ROWS_PAT32) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "r"
    then ASSUME_TAC(MATCH_MP SI_JOIN_VEC32 (REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] th))
    else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM HPOST_YVEC]) THEN
  HPOST_LAZY_W_TAC THEN
  X86_STEPS_TAC SI44_HPOST_EXEC (44--45) THEN
  MAP_EVERY (fun r ->
    MP_TAC(SPECL [`rsp0:int64`; `5376`; SI44_W; `s45:x86state`;
                  mk_small_numeral r] SI_SLICE_VEC32) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN DISCH_TAC) [0;1;2;3] THEN
  MAP_EVERY (fun r ->
    let n = if r = 0 then 44 else 44 + 7 * r in
    (if r = 0 then ALL_TAC else X86_STEPS_TAC SI44_HPOST_EXEC (n--(n+1))) THEN
    HPOST_CALL_TAC ("H_DEC"^string_of_int r) [`rsp0:int64`; `pc:num`; HPOST_ROW SI44_W r] (n+2) THEN
    SI_MAP_POLY_OF_TAC `mld_poly_decompose_lo_88` THEN
    X86_STEPS_TAC SI44_HPOST_EXEC ((n+3)--(n+5)) THEN
    HPOST_CALL_TAC ("H_W1P"^string_of_int r)
      [`word_add rsp0 (word 800):int64`; `rsp0:int64`; `pc:num`;
       mk_comb(`mld_poly_decompose_hi_88`,HPOST_ROW SI44_W r)] (n+6)) [0;1;2;3];;

let SI_ZERO_LO_SPLIT = WORD_BLAST
 `!x:int128. word_subword (word_subword (word_join x (word 0:int128):int256) (0,128):int128) (0,64):int64 = word 0 /\
             word_subword (word_subword (word_join x (word 0:int128):int256) (0,128):int128) (64,64):int64 = word 0`;;

let HPOST_W1_COEFF = prove
 (mk_forall(`r:num`,mk_forall(`j:num`,mk_imp(`j < 192`,
   mk_eq(mk_comb(SI44_W1,`192 * r + j`),
         list_mk_comb(`mld_polyw1_pack_88`,
           [mk_comb(`mld_poly_decompose_hi_88`,mk_comb(mk_comb(`mld_poly_of`,SI44_W),`r:num`));
            `j:num`]))))),
  REWRITE_TAC[mld_sign_w1] THEN SIMP_TAC[MLD_POLYVEC_PACK_COEFF; o_THM]);;

(*** w0 and w1 as vectors, c~, the challenge and its NTT: steps 72 to 92 ***)

let HPOST_PART3_TAC =
  SI_ROWS4_TAC `rsp0:int64` 5376 `s71:x86state`
    (subst [mk_comb(`mld_polyvec_map mld_poly_decompose_lo_88`,SI44_W),`V:num->int32`]
           HPOST_ROWS_PAT32) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "r"
    then ASSUME_TAC(MATCH_MP SI_JOIN_VEC32 (REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] th))
    else NO_TAC) THEN
  SUBGOAL_THEN (subst [SI44_W1,`P:num->byte`]
    `!r j. r < 4 /\ j < 192
           ==> read (memory :> bytes8 (word_add rsp0 (word ((1824 + 192 * r) + j)))) s71 =
               (P:num->byte) (192 * r + j)`) ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[HPOST_W1_COEFF] THEN
    UNDISCH_TAC `r < 4` THEN SPEC_TAC(`r:num`,`r:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "r"
    then ASSUME_TAC(MATCH_MP SI_JOIN_VEC8 th) else NO_TAC) THEN
  X86_STEPS_TAC SI44_HPOST_EXEC (72--72) THEN
  YMM_GHOST_TAC `s72:x86state` ["YMM0","ymm0_72"] THEN
  X86_STEPS_TAC SI44_HPOST_EXEC (73--82) THEN
  VERIF_NULL_TAC [`word_add rsp0 (word 512):int64`,`32`; `word_sub rsp0 (word 600):int64`,`576`] THEN
  VM_SPLIT128_TAC `word_sub rsp0 (word 16):int64` `s82:x86state` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SI_ZERO_LO_SPLIT]) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `!t. t < 768 ==> read (memory :> bytes8
         (word_add rsp0 (word (1824 + t)))) s = f t`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[ETA_AX; WORD_RULE `word_add (x:int64) (word 1824) =
                                  word_add (word_sub x (word 16)) (word 1840)`]
                      (MATCH_MP SIGN_READ_BYTES_OF_BYTES8_OFF th))
    else NO_TAC) THEN
  SUBGOAL_THEN `aligned 16 (word_sub rsp0 (word 16):int64)` ASSUME_TAC THENL
   [MATCH_MP_TAC ALIGNED_WORD_SUB THEN CONJ_TAC THENL
     [MATCH_MP_TAC(MP (ISPECL [`16`;`32`;`rsp0:int64`] ALIGNED_WORD_WEAKEN)
                      (EQT_ELIM(DIVIDES_CONV `16 divides 32`))) THEN
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `aligned 16 (word_add (word_sub (word_sub rsp0 (word 16)) (word 8)) (word 8):int64)`
   ASSUME_TAC THENL
   [REWRITE_TAC[WORD_RULE `word_add (word_sub (word_sub (x:int64) (word 16)) (word 8)) (word 8) =
                           word_sub x (word 16)`] THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  HPOST_FCALL_TAC "H_H44"
   [`read RDI s`; `32`; `read RDX s`; `64`; `read R8 s`; `768`;
    `word 0:int64`; `0`; `mu:num`; SI44_W1NUM; `0`] 83 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; MULT_CLAUSES;
    ARITH_RULE `64 + 768 = 832`; ARITH_RULE `8 * 64 = 512`;
    WORD_RULE `word_add (word_sub (x:int64) (word 16)) (word 528) = word_add x (word 512)`]) THEN
  SUBGOAL_THEN `read (memory :> bytes (word_add rsp0 (word 512),32)) s83 = C` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_var(rhs(concl th)) && name_of(rhs(concl th)) = "C"
                          then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[mld_sign_ctilde; ARITH_RULE `64 + 4 * 192 = 832`; ARITH_RULE `4 * 192 = 768`] THEN
    FIRST_ASSUM(fun th -> if can (term_match []
       `read (memory :> bytes (word_add rsp0 (word 512),32)) s83 = num_of_bytelist l`) (concl th)
       then ACCEPT_TAC th else NO_TAC);
    ALL_TAC] THEN
  X86_STEPS_TAC SI44_HPOST_EXEC (84--84) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE `word_add (word_sub (x:int64) (word 16)) (word 16) = x`]) THEN
  X86_STEPS_TAC SI44_HPOST_EXEC (85--88) THEN
  HPOST_FCALL_TAC "H_CHAL" [`read RDI s`; `read RSI s`; `C:num`] 89 THEN
  X86_STEPS_TAC SI44_HPOST_EXEC (90--91) THEN
  HPOST_FCALL_TAC "H_NTT" [`read RDI s`; `mld_poly_challenge 39 32 C`] 92 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  VERIF_EMPTY_REGIONS_TAC THEN RIT_END_TAC;;

let SI44_HPOST = prove
 (SI44_HPOST_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mcs = CONJ_PAIR th in
    MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
     [SI44_RED14,"H_RED0"; SI44_RED15,"H_RED1"; SI44_RED16,"H_RED2"; SI44_RED17,"H_RED3";
      SI44_CQ18,"H_CQ0"; SI44_CQ19,"H_CQ1"; SI44_CQ20,"H_CQ2"; SI44_CQ21,"H_CQ3";
      SI44_DEC22,"H_DEC0"; SI44_DEC24,"H_DEC1"; SI44_DEC26,"H_DEC2"; SI44_DEC28,"H_DEC3";
      SI44_W1P23,"H_W1P0"; SI44_W1P25,"H_W1P1"; SI44_W1P27,"H_W1P2"; SI44_W1P29,"H_W1P3";
      MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_INV";
      MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL,"H_NTT";
      MP (SPEC_ALL MLDSA_NATIVE_H_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) mcs,"H_H44";
      MP (SPEC_ALL MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th,
      "H_CHAL"]) THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (C:num) (mf:int64) (mc:int64) (pc:num).
      f_ev_hp rsp0 C mf mc pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `rho:num`; `rhop:num`;
                       `kappa:num`; `mu:num`; `C:num`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst SI44_HPOST_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SI_ALIGNED16_TAC [0xa0; 0xb0; 0xc0; 0xd0; 0x1500; 0x1900; 0x1d00; 0x2100] THEN
  FULL_INIT_TAC THEN HPOST_PART1_TAC THEN HPOST_PART2_TAC THEN HPOST_PART3_TAC);;

(* ------------------------------------------------------------------------- *)
(* The start of an attempt (HEAD), from join2 with the number n of the       *)
(* attempt in RCX: n saved at rsp0 + 0x190, the pointer to rho'' and kappa = *)
(* 4 n (16 bits) at rsp0 + 0x80 and + 0x88, rho copied from rsp0 + 0x14e0 to *)
(* the seed buffer at rsp0 + 0xa0, the four columns of the product with the  *)
(* matrix (YCOL 0 .. 3) and HPOST, to after the NTT of the challenge, as     *)
(* gcc's SIGN44_HEAD.                                                        *)
(* ------------------------------------------------------------------------- *)

let HEAD_Y = `mld_sign_y mld_poly_uniform_gamma1_17 rhop (4 * n)`;;
let HEAD_W = list_mk_comb(`mld_sign_w 4`,[SI44_A; HEAD_Y]);;
let HEAD_W1 = mk_comb(`mld_sign_w1 (mld_polyw1_pack_88 o mld_poly_decompose_hi_88) 192`,HEAD_W);;
let HEAD_CT = mk_comb(`mld_sign_ctilde 4 192 mu`,HEAD_W1);;

let SI44_HEAD_STMT = parse_term(subst_tokens
  ["@MC@",image_mc; "@W@",string_of_term HEAD_W; "@W1@",string_of_term HEAD_W1;
   "@CT@",string_of_term HEAD_CT]
 "!mf mc ea el ev.
     memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e rsp0 n rho rhop mu C pc.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          aligned 32 rsp0 /\\ n < 16382 /\\ mld_matrix_terminates 4 4 rho /\\
          num_of_bytelist(list_of_seq (@CT@) 32) = C /\\
          mld_poly_challenge_terminates 39 32 C /\\
          ALL (nonoverlapping (word_sub rsp0 (word 1471),11999))
              [(word pc,libmldsa_size);
               (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
           (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + mldsa44_signature_internal_join2) /\\
                read RSP s = rsp0 /\\ read RCX s = word n /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes (word_add rsp0 (word 5344),32)) s = rho /\\
                read (memory :> bytes (word_add rsp0 (word 672),64)) s = mu /\\
                read (memory :> bytes (word_add rsp0 (word 736),64)) s = rhop /\\
                read events s = e)
           (\\s. read RIP s = word (pc + mldsa44_signature_internal_after_mldsa_poly_ntt_2) /\\
                read RSP s = rsp0 /\\ read R12 s = word 0x0380200100000000 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes64 (word_add rsp0 (word 400))) s = word n /\\
                read (memory :> bytes64 (word_add rsp0 (word 128))) s = word_add rsp0 (word 736) /\\
                read (memory :> bytes16 (word_add rsp0 (word 136))) s = word (4 * n) /\\
                (!i. i < 1024 ==> read (memory :> bytes32 (word_add rsp0 (word (5376 + 4 * i)))) s =
                                  mld_polyvec_map mld_poly_decompose_lo_88 (@W@) i) /\\
                (!j. j < 768 ==> read (memory :> bytes8 (word_add rsp0 (word (1824 + j)))) s =
                                 (@W1@) j) /\\
                read (memory :> bytes (word_add rsp0 (word 512),32)) s = C /\\
                (!k. k < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (9472 + 4 * k)))) s =
                                 mld_poly_ntt (mld_poly_challenge 39 32 C) k) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events rsp0 rho C mf mc pc /\\
                   memaccess_inbounds e2
                    [word_sub rsp0 (word 1471),11999;
                     word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa44_signature_internal_consts),32;
                     word(pc + mldsa44_poly_challenge_consts),64;
                     word(pc + mldsa_poly_ntt_consts),256;
                     word(pc + mldsa_poly_invntt_tomont_consts),448]
                    [word_sub rsp0 (word 1471),11999]))
           (MAYCHANGE [RSP; RBX; R12; R13; R14; R15] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(word_sub rsp0 (word 1471),1471);
                       memory :> bytes(word_add rsp0 (word 16),8);
                       memory :> bytes(word_add rsp0 (word 128),16);
                       memory :> bytes(word_add rsp0 (word 160),64);
                       memory :> bytes(word_add rsp0 (word 400),8);
                       memory :> bytes(word_add rsp0 (word 512),32);
                       memory :> bytes(word_add rsp0 (word 800),1024);
                       memory :> bytes(word_add rsp0 (word 1824),768);
                       memory :> bytes(word_add rsp0 (word 2592),66);
                       memory :> bytes(word_add rsp0 (word 4320),1024);
                       memory :> bytes(word_add rsp0 (word 5376),4096);
                       memory :> bytes(word_add rsp0 (word 9472),1024)])");;

let SI44_HEAD_EXEC = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
  [(layout "mldsa44_signature_internal_join2", layout "mldsa44_signature_internal_after_mldsa_poly_ntt_2")];;

let HEAD_ALLOWED = [`rsp0:int64`; `rho:num`; `C:num`; `mf:int64`; `mc:int64`; `pc:num`];;

let HEAD_CALL_TAC name ilist n =
  REMOVE_THEN name (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (VM_MC,SI44_HEAD_EXEC,0x0,VM_MC,th)
      (`e:(uarch_event)list`::ilist) n THENL
     [REPEAT CONJ_TAC THEN
      TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
      TRY(FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
      VM_PRE_TAC HEAD_ALLOWED;
      LABEL_TAC name th]);;

(* the 16-bit store of 4 n *)
let HEAD_SX_ZX = WORD_BLAST `!v:int64. (word_sx v:int32) = word_zx v`;;
let HEAD_KAPPA = prove
 (`!n. n < 16382
       ==> word (val (word_zx (word_sx (word (0 + 4 * val (word n:int64)):int64):int32):int64) MOD 65536):int16 =
           word (4 * n)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[HEAD_SX_ZX; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_64; DIMINDEX_32; ADD_CLAUSES] THEN
  SUBGOAL_THEN `n < 2 EXP 64 /\ 4 * n < 2 EXP 32 /\ 4 * n < 2 EXP 64 /\ 4 * n < 65536`
    STRIP_ASSUME_TAC THENL [UNDISCH_TAC `n < 16382` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT]);;

let HEAD_TAC =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
     [MP (SPEC_ALL SI44_YCOL0) th,"H_YC0"; MP (SPEC_ALL SI44_YCOL1) th,"H_YC1";
      MP (SPEC_ALL SI44_YCOL2) th,"H_YC2"; MP (SPEC_ALL SI44_YCOL3) th,"H_YC3";
      MP (SPEC_ALL SI44_HPOST) th,"H_HP"]) THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (rho:num) (C:num) (mf:int64) (mc:int64) (pc:num).
      f_ev_head rsp0 rho C mf mc pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `n:num`; `rho:num`; `rhop:num`;
                       `mu:num`; `C:num`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst SI44_HEAD_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SI_ALIGNED16_TAC [0xa0; 0xb0; 0x14e0; 0x14f0] THEN
  GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
  FULL_INIT_TAC THEN
  MAP_EVERY (fun i ->
    MP_TAC(SPECL [`word_add rsp0 (word 5344):int64`; `32`; `rho:num`; mk_small_numeral i; `s0:x86state`]
             SIGN_BYTES128_OF_BYTES) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC) [0;1] THEN
  X86_STEPS_TAC SI44_HEAD_EXEC (1--12) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO; DIV_1]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP HEAD_KAPPA (ASSUME `n < 16382`)]) THEN
  SUBGOAL_THEN `rho < 2 EXP (8 * 32)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes (word_add rsp0 (word 5344),32)) s0 = rho`) (concl th)
      then SUBST1_TAC(SYM th) else NO_TAC) THEN REWRITE_TAC[READ_BYTES_BOUND; READ_COMPONENT_COMPOSE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`word_add rsp0 (word 160):int64`; `rho:num`; `2`; `s12:x86state`] SIGN_BYTES_OF_BYTES128) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0; DIV_1] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `rho MOD 2 EXP (128 * 2) = rho` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN FIRST_ASSUM(MP_TAC o check (fun th -> concl th = `rho < 2 EXP (8 * 32)`)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN DISCH_TAC THEN
  HEAD_CALL_TAC "H_YC0" [`rsp0:int64`; `rho:num`; `rhop:num`; `4 * n`; `pc:num`] 13 THEN
  MAP_EVERY (fun j ->
    let n0 = 14 + 4 * (j - 1) in
    X86_STEPS_TAC SI44_HEAD_EXEC (n0--n0) THEN
    RULE_ASSUM_TAC(fun th -> if can (term_match [] `read R14 s = x`) (concl th)
                             then CONV_RULE(RAND_CONV WORD_REDUCE_CONV) th else th) THEN
    X86_STEPS_TAC SI44_HEAD_EXEC ((n0+1)--(n0+2)) THEN
    HEAD_CALL_TAC ("H_YC"^string_of_int j) [`rsp0:int64`; `rho:num`; `rhop:num`; `4 * n`; `pc:num`]
      (n0+3)) [1;2;3] THEN
  X86_STEPS_TAC SI44_HEAD_EXEC (26--26) THEN
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read R14 s = x`) (concl th)
                           then CONV_RULE(RAND_CONV WORD_REDUCE_CONV) th else th) THEN
  X86_STEPS_TAC SI44_HEAD_EXEC (27--28) THEN
  HEAD_CALL_TAC "H_HP" [`rsp0:int64`; `rho:num`; `rhop:num`; `4 * n`; `mu:num`; `C:num`; `pc:num`] 29 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  RIT_END_TAC;;

let SI44_HEAD = prove(SI44_HEAD_STMT, HEAD_TAC);;

(* ------------------------------------------------------------------------- *)
(* A whole attempt (ATT), from join2 to the decision after the cleanup: to   *)
(* join28 on success (r = 13) and to the count of the attempts at +0x2828    *)
(* otherwise, by cases on the result r of mld_sign_attempt_declass, as       *)
(* gcc's SIGN44_ATT: r < 4 (z_r fails, ZPRE then ZIT), 4 <= r < 12 (check    *)
(* r - 4 of the rows fails, ZPRE, RPRE then RIT), 12 (too many hints) and 13 *)
(* (success), both through TAIL; then CLEAN.                                 *)
(* ------------------------------------------------------------------------- *)

let ATT_A = SI44_A;;
let ATT_Y = HEAD_Y;;
let ATT_W = HEAD_W;;
let ATT_W1 = HEAD_W1;;
let ATT_CPH = `mld_poly_ntt (mld_poly_challenge 39 32 C)`;;
let ATT_S1H = subst [`skb:num->byte`,`skb:num->byte`] SI44_S1H;;
let ATT_R0 = list_mk_comb(`mld_sign_r0`,[`mld_poly_decompose_lo_88`; ATT_W; SI44_S2H; ATT_CPH]);;
let ATT_CT0 = list_mk_comb(`mld_sign_ct0`,[SI44_T0H; ATT_CPH]);;
let ATT_CT = mk_comb(`mld_sign_ctilde 4 192 mu`,ATT_W1);;
let ATT_SIGATT = list_mk_comb(
 `mld_sign_attempt_sig 4 4 32 39 mld_poly_uniform_gamma1_17 mld_polyz_pack_17
   576 (mld_polyw1_pack_88 o mld_poly_decompose_hi_88) 192
   mld_poly_decompose_lo_88 mld_polyvec_make_hint_88 80`,
  [ATT_A; SI44_S1H; SI44_S2H; SI44_T0H; `mu:num`; `rhop:num`; `4 * n`]);;

let SI44_ATT_STMT = parse_term(subst_tokens
  ["@MC@",image_mc; "@SIGATT@",string_of_term ATT_SIGATT;
   "@S1H@",string_of_term SI44_S1H; "@S2H@",string_of_term SI44_S2H; "@T0H@",string_of_term SI44_T0H;
   "@NX@",string_of_int(layout "mldsa44_signature_internal" + 0x2828)]
 "!mf mc ea el ev.
     memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig sk skb rsp0 rho mu rhop n C r x b pc.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          aligned 32 rsp0 /\\ n < 16382 /\\ mld_matrix_terminates 4 4 rho /\\
          mld_sign_attempt_declass 4 4 32 39 mld_poly_uniform_gamma1_17
           130994 95154 95232 (mld_polyw1_pack_88 o mld_poly_decompose_hi_88)
           192 mld_poly_decompose_lo_88 mld_polyvec_make_hint_88 80
           (mld_polyvec_matrix_expand 4 rho) (@S1H@) (@S2H@) (@T0H@)
           mu rhop (4 * n) = (C,r,x,b) /\\
          mld_poly_challenge_terminates 39 32 C /\\
          ALL (nonoverlapping (word_sub rsp0 (word 1471),11999))
              [(sig,2420); (sk,2560); (word pc,libmldsa_size);
               (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\\
          ALL (nonoverlapping (sig,2420))
              [(sk,2560); (word pc,libmldsa_size);
               (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
           (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + mldsa44_signature_internal_join2) /\\
                read RSP s = rsp0 /\\ read RCX s = word n /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes64 (word_add rsp0 (word 8))) s = sig /\\
                read (memory :> bytes64 (word_add rsp0 (word 24))) s = word_add sig (word 2336) /\\
                read (memory :> bytes64 (word_add rsp0 (word 32))) s = word_add sk (word 512) /\\
                read (memory :> bytes64 (word_add rsp0 (word 64))) s = word_add sk (word 896) /\\
                read (memory :> bytes64 (word_add rsp0 (word 96))) s = word_add sk (word 128) /\\
                read (memory :> bytes64 (word_add rsp0 (word 392))) s = word_add sig (word 39) /\\
                read (memory :> bytes (word_add rsp0 (word 5344),32)) s = rho /\\
                read (memory :> bytes (word_add rsp0 (word 672),64)) s = mu /\\
                read (memory :> bytes (word_add rsp0 (word 736),64)) s = rhop /\\
                (!k. k < 2560 ==> read (memory :> bytes8 (word_add sk (word k))) s = skb k) /\\
                read events s = e)
           (\\s. read RIP s =
                (if r = 13 then word (pc + mldsa44_signature_internal_join28)
                 else word (pc + @NX@)) /\\
                read RSP s = rsp0 /\\ read R15 s = word 0 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes64 (word_add rsp0 (word 400))) s = word n /\\
                (r = 13
                 ==> !t. t < 2420
                         ==> read (memory :> bytes8 (word_add sig (word t))) s = (@SIGATT@) t) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events sig sk rsp0 rho C r x b mf mc pc /\\
                   memaccess_inbounds e2
                    [sig,2420; sk,2560; word_sub rsp0 (word 1471),11999;
                     word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192;
                     word(pc + rodata_mld_zetas),1024;
                     word(pc + mldsa44_signature_internal_consts),32;
                     word(pc + mldsa44_poly_challenge_consts),64;
                     word(pc + mldsa_poly_ntt_consts),256;
                     word(pc + mldsa_poly_invntt_tomont_consts),448]
                    [sig,2420; word_sub rsp0 (word 1471),11999]))
           (MAYCHANGE [RSP; RBX; R10; R12; R13; R14; R15] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(sig,2420);
                       memory :> bytes(word_sub rsp0 (word 1471),1471);
                       memory :> bytes(word_add rsp0 (word 16),8);
                       memory :> bytes(word_add rsp0 (word 128),16);
                       memory :> bytes(word_add rsp0 (word 152),8);
                       memory :> bytes(word_add rsp0 (word 160),208);
                       memory :> bytes(word_add rsp0 (word 400),8);
                       memory :> bytes(word_add rsp0 (word 408),8);
                       memory :> bytes(word_add rsp0 (word 416),66);
                       memory :> bytes(word_add rsp0 (word 512),32);
                       memory :> bytes(word_add rsp0 (word 800),1024);
                       memory :> bytes(word_add rsp0 (word 1824),768);
                       memory :> bytes(word_add rsp0 (word 2592),680);
                       memory :> bytes(word_add rsp0 (word 3296),1024);
                       memory :> bytes(word_add rsp0 (word 4320),1024);
                       memory :> bytes(word_add rsp0 (word 5376),4096);
                       memory :> bytes(word_add rsp0 (word 9472),1024)])");;

let SI44_ATT_EXEC = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
  [(layout "mldsa44_signature_internal_join2", layout "mldsa44_signature_internal" + 0x2828);
   layout_range "plt_memset"];;

let ATT_ALLOWED =
  [`sig:int64`; `sk:int64`; `rsp0:int64`; `rho:num`; `C:num`; `r:num`;
   `x:num->int32`; `b:num->byte`; `mf:int64`; `mc:int64`; `pc:num`];;

let ATT_CALL_TAC name ilist n =
  REMOVE_THEN name (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (VM_MC,SI44_ATT_EXEC,0x0,VM_MC,th)
      (`e:(uarch_event)list`::ilist) n THENL
     [REPEAT CONJ_TAC THEN
      TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
      TRY(FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
      TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
      VM_PRE_TAC ATT_ALLOWED;
      LABEL_TAC name th]);;

let ATT_MID = parse_term(subst_tokens ["@SIGATT@",string_of_term ATT_SIGATT]
 "\\s. read RSP s = rsp0 /\\
      (word_zx (read RBX s) = (word 0:byte) <=> ~(r = 13)) /\\
      read R15 s = word 0 /\\
      (read DF s <=> false) /\\
      read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
      read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
      read (memory :> bytes(ea,el)) s = ev /\\
      read (memory :> bytes64 (word_add rsp0 (word 400))) s = word n /\\
      (r = 13
       ==> !t. t < 2420
               ==> read (memory :> bytes8 (word_add sig (word t))) s = (@SIGATT@) t)");;

let ATT_END_TAC = REPEAT CONJ_TAC THEN (RIT_MAYCHANGE_TAC ORELSE SI_DISCHARGE_TAC 1471);;

let ATT_PC_TAC =
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read RIP s = x`) (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NUM_LT_CONV THENC REWRITE_CONV[]) th else th) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `read RIP s = x`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC;;

(* the memaccess goal of a path, as at the end of SI_DISCHARGE_TAC: the
   facts of the callees split with their definitions (only equations of
   event-list variables, so that numeric equations such as r = 13 are left
   alone), the frame normalized to rsp0 - 1471 *)
let ATT_MEMACCESS_TAC =
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
  SIGN_BETA_ALL_TAC THEN SI_FB_NORM_TAC 1471 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC]) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN split_tac THEN
  RULE_ASSUM_TAC(fun th -> if (match strip_comb(concl th) with
      (Const("memaccess_inbounds",_),_) -> true | _ -> false)
     then REWRITE_RULE[MEMACCESS_INBOUNDS_APPEND] th else th) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) &&
      (match strip_comb(fst(dest_conj(concl th))) with
         (Const("memaccess_inbounds",_),_) -> true | _ -> false)
     then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   BYTE_IDX_DISCHARGE_TAC DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

let ATT_PATH_DISCHARGE_TAC =
  SIGN_BETA_ALL_TAC THEN SIGN_SELECT_TAC THEN SIGN_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [SIGN_PATH_UNIFY_TAC; ATT_MEMACCESS_TAC];;

let ATT_FIN_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ZX_0] THEN
  REPEAT CONJ_TAC THEN (RIT_MAYCHANGE_TAC ORELSE ATT_PATH_DISCHARGE_TAC);;

(*** z_r fails, r < 4 ***)

let ATT_ZCASE_TAC =
  SUBGOAL_THEN `r <= 4 /\ ~(r = 13)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `r < 4` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `r < 4 ==> P`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ATT_CALL_TAC "H_ZPRE"
   [`r:num`; `sig:int64`; `sk:int64`; `skb:num->byte`; `rsp0:int64`;
    `rhop:num`; `4 * n`; ATT_CPH; `pc:num`] 2 THEN
  ATT_PC_TAC THEN
  ATT_CALL_TAC "H_ZIT"
   [`F`; `sig:int64`; `sk:int64`; `skb:num->byte`; `rsp0:int64`;
    `rhop:num`; `4 * n`; `r:num`; ATT_CPH; `pc:num`] 3 THEN
  ATT_PC_TAC THEN
  X86_STEPS_TAC SI44_ATT_EXEC (4--4) THEN
  ATT_FIN_TAC;;

let ATT_TEMPLATE =
 `\(sig:int64) (sk:int64) (rsp0:int64) (rho:num) (C:num) (r:num) (x:num->int32) (b:num->byte)
   (mf:int64) (mc:int64) (pc:num).
   APPEND (f_ev_cl sig sk rsp0 rho C r x b mf mc pc)
    (APPEND
      (if r < 4 then f_ev_pz sig sk rsp0 rho C r x b mf mc pc
       else if r < 12
       then if EVEN (r - 4) then f_ev_pw1 sig sk rsp0 rho C r x b mf mc pc
            else f_ev_pw2 sig sk rsp0 rho C r x b mf mc pc
       else f_ev_pt sig sk rsp0 rho C r x b mf mc pc)
      (f_ev_hd sig sk rsp0 rho C r x b mf mc pc))
   :(uarch_event)list`;;

let ATT_SETUP_TAC =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mcs = CONJ_PAIR th in
    MAP_EVERY (fun (th,n) -> SI_ASSUME_CALLEE_TAILED_TAC th n)
     [MP (SPEC_ALL SI44_HEAD) th,"H_HEAD"; MP (SPEC_ALL SI44_ZPRE) th,"H_ZPRE";
      MP (SPEC_ALL SI44_ZIT) th,"H_ZIT"; SI44_RPRE,"H_RPRE"; SI44_RIT,"H_RIT";
      SI44_TAIL,"H_TAIL"; MP (SPEC_ALL SI44_CLEAN) ms,"H_CLEAN"]) THEN
  CONCRETIZE_F_EVENTS_TAC ATT_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `sk:int64`; `skb:num->byte`; `rsp0:int64`;
    `rho:num`; `mu:num`; `rhop:num`; `n:num`; `C:num`; `r:num`; `x:num->int32`;
    `b:num->byte`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst SI44_ATT_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
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

(*** check r - 4 of the rows fails, 4 <= r < 12 ***)

let ATT_ROWSLICE_TAC m st =
  MP_TAC(SPECL [`rsp0:int64`; `5376`; `1024`; `mld_poly_decompose_lo_88`; ATT_W; m; st]
               SIGN_ROW_SLICE) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [m; st]
             `!k. 256 * m <= k /\ k < 1024
                  ==> read (memory :> bytes32 (word_add rsp0 (word (5376 + 4 * k)))) st = Q k`)
           (concl th)
    then REWRITE_TAC[th] else NO_TAC) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC];;

let ATT_WCASE_TAC =
  SUBGOAL_THEN `(r - 4) DIV 2 <= 4 /\ (r - 4) DIV 2 < 4 /\ ~(r = 13) /\
                2 * (r - 4) DIV 2 <= r - 4`
   STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `r < 12` THEN UNDISCH_TAC `4 <= r` THEN
    SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [ATT_R0; ATT_CT0; `95154`; `95232`; `r - 4`;
                `(r - 4) DIV 2`] SIGN_ROWS_GOOD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `j:num` o REWRITE_RULE[ASSUME `4 <= r`] o
      check (fun th -> can (term_match []
        `4 <= r ==> (!j. j < r - 4 /\ j < 8 ==> P j)`) (concl th))) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `j < r - 4` THEN UNDISCH_TAC `r < 12` THEN ARITH_TAC;
    DISCH_TAC] THEN
  ATT_CALL_TAC "H_ZPRE"
   [`4`; `sig:int64`; `sk:int64`; `skb:num->byte`; `rsp0:int64`;
    `rhop:num`; `4 * n`; ATT_CPH; `pc:num`] 2 THEN
  ATT_PC_TAC THEN
  ATT_CALL_TAC "H_RPRE"
   [`(r - 4) DIV 2`; `sk:int64`; `skb:num->byte`; `rsp0:int64`; ATT_W; ATT_CPH; `pc:num`] 3 THEN
  ATT_PC_TAC THEN
  ATT_ROWSLICE_TAC `(r - 4) DIV 2` `s3:x86state` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `4 <= r /\ r < 12 ==> ~(P = word 0:int32)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `EVEN(r - 4)` THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `~(mld_poly_chknorm (if EVEN(r - 4) then a else b) (word w) = word 0)`)
      (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ATT_CALL_TAC "H_RIT"
     [`F`; `F`; `sk:int64`; `skb:num->byte`; `rsp0:int64`; `(r - 4) DIV 2`; ATT_W; ATT_CPH;
      `pc:num`] 4;
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
    ATT_CALL_TAC "H_RIT"
     [`T`; `F`; `sk:int64`; `skb:num->byte`; `rsp0:int64`; `(r - 4) DIV 2`; ATT_W; ATT_CPH;
      `pc:num`] 4] THEN
  ATT_PC_TAC THEN
  X86_STEPS_TAC SI44_ATT_EXEC (5--7) THEN
  ATT_FIN_TAC;;

(*** the hints, r = 12 (too many) or 13 (success) ***)

let SI_BYTES8_OF_READ_BYTES0 = SIGN_BYTES8_OF_READ_BYTES;;

let ATT_TCASE_TAC =
  SUBGOAL_THEN `12 <= r /\ 4 <= 4` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(r < 12)` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [ATT_R0; ATT_CT0; `95154`; `95232`; `8`; `4`] SIGN_ROWS_GOOD) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[LE_REFL] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `j:num` o REWRITE_RULE[ASSUME `4 <= r`] o
      check (fun th -> can (term_match []
        `4 <= r ==> (!j. j < r - 4 /\ j < 8 ==> P j)`) (concl th))) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `12 <= r` THEN UNDISCH_TAC `j < 8` THEN ARITH_TAC;
    DISCH_TAC] THEN
  ATT_CALL_TAC "H_ZPRE"
   [`4`; `sig:int64`; `sk:int64`; `skb:num->byte`; `rsp0:int64`;
    `rhop:num`; `4 * n`; ATT_CPH; `pc:num`] 2 THEN
  ATT_PC_TAC THEN
  ATT_CALL_TAC "H_RPRE"
   [`4`; `sk:int64`; `skb:num->byte`; `rsp0:int64`; ATT_W; ATT_CPH; `pc:num`] 3 THEN
  ATT_PC_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `(if 12 <= r then p else q) = (x:num->int32)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `(if 12 <= r then p else q) = (b:num->byte)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!j. j < 768
        ==> read (memory :> bytes8 (word_add rsp0 (word (1824 + j)))) s3 =
            (b:num->byte) j`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(fun th ->
      if is_var(rhs(concl th)) && name_of(rhs(concl th)) = "b"
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[mld_sign_hint_w1] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ATT_CALL_TAC "H_TAIL"
   [`sig:int64`; `rsp0:int64`; `read RBX s`; `C:num`; `x:num->int32`; `b:num->byte`; `pc:num`] 4 THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `12 <= r ==> (r = 13 <=> P)`) (concl th))) THEN
  ASM_REWRITE_TAC[NOT_LT] THEN DISCH_TAC THEN
  ASM_CASES_TAC `r = 13` THENL
   [SUBGOAL_THEN `mld_hint_count (mld_polyvec_make_hint_88 x b) 1024 <= 80` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if is_iff(concl th) && lhs(concl th) = `r = 13`
                            then ACCEPT_TAC(EQ_MP th (ASSUME `r = 13`)) else NO_TAC); ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `mld_hint_count (mld_polyvec_make_hint_88 x b) 1024 <= 80`]) THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [`sig:int64`; `C:num`] `read (memory :> bytes (sig,32)) s = C`) (concl th)
      then FIRST_ASSUM(fun cth ->
             if is_var(rhs(concl cth)) && name_of(rhs(concl cth)) = "C"
             then ASSUME_TAC(MATCH_MP SI_BYTES8_OF_READ_BYTES0 (TRANS th (SYM cth)))
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
    (RIT_MAYCHANGE_TAC ORELSE ATT_PATH_DISCHARGE_TAC);
    SUBGOAL_THEN `~(mld_hint_count (mld_polyvec_make_hint_88 x b) 1024 <= 80)` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if is_iff(concl th) && lhs(concl th) = `r = 13`
                            then MP_TAC th else NO_TAC) THEN
      REWRITE_TAC[ASSUME `~(r = 13)`]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(mld_hint_count (mld_polyvec_make_hint_88 x b) 1024 <= 80)`]) THEN
    X86_STEPS_TAC SI44_ATT_EXEC (5--5) THEN
    ATT_FIN_TAC];;

let ATT_PATHS_TAC =
  ASM_CASES_TAC `r < 4` THENL
   [ATT_ZCASE_TAC;
    SUBGOAL_THEN `4 <= r /\ 4 <= 4` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~(r < 4)` THEN ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `4 <= r ==> (!i. i < 4 ==> P i)`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_CASES_TAC `r < 12` THENL [ATT_WCASE_TAC; ATT_TCASE_TAC]];;

let ATT_CLEAN_TAC =
  FULL_INIT_TAC THEN
  ATT_CALL_TAC "H_CLEAN" [`r = 13`; `rsp0:int64`; `read RBX s`; `pc:num`] 1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN (RIT_MAYCHANGE_TAC ORELSE SI_DISCHARGE_TAC 1471);;

let SI44_ATT = prove
 (SI44_ATT_STMT,
  ATT_SETUP_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa44_signature_internal_join27` ATT_MID THEN
  CONJ_TAC THENL
   [FULL_INIT_TAC THEN
    ATT_CALL_TAC "H_HEAD"
     [`rsp0:int64`; `n:num`; `rho:num`; `rhop:num`; `mu:num`; `C:num`; `pc:num`] 1 THEN
    ATT_PATHS_TAC;
    ATT_CLEAN_TAC]);;
