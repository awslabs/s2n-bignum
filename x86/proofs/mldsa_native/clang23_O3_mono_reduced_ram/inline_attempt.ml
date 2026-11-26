(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Loops that clang 23 -O3 inlines into mldsa-native's signing attempt       *)
(* (mld_attempt_signature_generation within mldsaNN_signature_internal) in   *)
(* the monolithic reduced-RAM build, as lemmas of the form of those of       *)
(* inline_sign.ml: from the head of a loop to its exit, with the stack       *)
(* pointer rsp0 of the caller and the buffers at fixed offsets from it, so   *)
(* that the proofs of the 44, 65 and 87 functions use them as subroutine     *)
(* theorems. A loop over the k-th polynomial of a vector is often addressed  *)
(* as [rsp + rax * 4 + d] with RAX running from r0 = 256 k, so that the      *)
(* polynomial is at rsp0 + d + 4 r0; when d is negative the simulator forms  *)
(* the address with the displacement 2^64 + d, and the tactics assume the    *)
(* alias of that form with the address in the frame before they step.        *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_verify.ml";;
needs "x86/proofs/utils/mldsa_native_sampling.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "x86/proofs/utils/mldsa_native_top.ml";;

(* The numeral of a displacement as the simulator has it. *)
let disp_num d =
  if d < 0 then string_of_num (num_of_string "18446744073709551616" -/ Num.num_of_int (-d))
  else string_of_int d;;

(* The index expression r0 + s * i (as text), "s * i" for r0 = 0. *)
let idx_expr r0 s =
  let si = if s = 1 then "(i:num)" else Printf.sprintf "%d * i" s in
  if r0 = 0 then si else Printf.sprintf "%d + %s" r0 si;;

(* ------------------------------------------------------------------------- *)
(* mld_poly_decompose (gamma2 = (q - 1) / 88) of the polynomial at rsp0 + wb, *)
(* one coefficient per iteration: the low part a0 replaces a, the high part  *)
(* a1 is stored at rsp0 + w1b. RAX is r0 + i, the addresses [rsp + rax * 4 + *)
(* wd] and [rsp + rax * 4 + w1d] with wb = wd + 4 r0 and w1b = w1d + 4 r0.   *)
(* ------------------------------------------------------------------------- *)

(* The low part as the code computes it: a0 = a + a1 * (-2 gamma2) by IMUL
   and LEA, then a0 - q if (q - 1) / 2 - a0 is negative; the product is
   generalized before the bit-blasting (DECOMPOSE_LO_88_ALT has the same). *)
let DECOMP_LO_LANE_TAC (reg:term) (v:term) =
  FIRST_X_ASSUM(fun th ->
    let l,r = dest_eq(concl th) in
    if (try rand(rator l) = reg with Failure _ -> false) &&
       is_comb r && rator r = `word_zx:int32->int64` && free_in v r then
      let t = rand r and y = genvar(type_of v) in
      let ty = subst[y,v] t in
      let lemma = prove
       (mk_forall(y,mk_eq(ty,mk_comb(`mld_decompose_lo_88`,y))),
        GEN_TAC THEN REWRITE_TAC[DECOMPOSE_LO_88_ALT; mld_ct_sel; mld_ct_cmask_neg] THEN
        CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
        REWRITE_TAC[MULT_CLAUSES; WORD_VAL; WORD_ZX_ZX_32_64_32] THEN
        SPEC_TAC(mk_comb(mk_comb(`word_mul:int32->int32->int32`,mk_comb(`mld_decompose_hi_88`,y)),
                         `word 4294776832:int32`),`p:int32`) THEN
        GEN_TAC THEN BITBLAST_TAC) in
      ASSUME_TAC th THEN RULE_ASSUM_TAC(REWRITE_RULE[lemma])
    else NO_TAC);;

let DECOMP88_STMT fn loop exit wd w1d r0 =
  let wb = wd + 4 * r0 and w1b = w1d + 4 * r0 in
  parse_term(Printf.sprintf
  "exists f_events.
  forall e rsp0 pc (x:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    PAIRWISE nonoverlapping
     [(word_add rsp0 (word %d),1024); (word_add rsp0 (word %d),1024); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word %d /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = x i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word %d /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s =
                               mld_poly_decompose_lo_88 x i) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s =
                               mld_poly_decompose_hi_88 x i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 pc /\\
                 memaccess_inbounds e2 [word_add rsp0 (word %d),1024; word_add rsp0 (word %d),1024]
                                       [word_add rsp0 (word %d),1024; word_add rsp0 (word %d),1024]))
         (MAYCHANGE [RIP; RAX; RCX; RDX; RSI] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes(word_add rsp0 (word %d),1024);
                     memory :> bytes(word_add rsp0 (word %d),1024)])"
  wb w1b image_mc fn loop r0 wb fn exit (r0 + 256) wb w1b wb w1b wb w1b wb w1b);;

let DECOMP88_TAC exec fn loop exit wd w1d r0 =
  let wb = wd + 4 * r0 and w1b = w1d + 4 * r0 in
  let idx = idx_expr r0 1 in
  let alias d b =
    if d >= 0 then ALL_TAC else
    ALIAS_ASSUME_TAC
     [Printf.sprintf "word_add rsp0 (word (4 * (%s) + %s)):int64 = word_add rsp0 (word (%d + 4 * i))"
        idx (disp_num d) b] in
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (pc:num).
      APPEND (f_ev_epil rsp0 pc)
       (APPEND (ENUMERATEL 256 (\i. f_ev_loop rsp0 pc i)) (f_ev_prol rsp0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `pc:num`; `x:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; PAIRWISE; ALL; fst exec;
              mld_poly_decompose_lo_88; mld_poly_decompose_hi_88] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read RSP s = rsp0 /\\
          read RAX s = word (%s) /\\
          (!j. i <= j /\\ j < 256
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = x j) /\\
          (!j. j < i
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s =
                   mld_decompose_lo_88 (x j)) /\\
          (!j. j < i
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s =
                   mld_decompose_hi_88 (x j))" idx wb wb w1b)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ONE_INPUT_SPLIT] o
      check (fun th -> is_forall(concl th) &&
        free_in `x:num->int32` (concl th) &&
        not(free_in `mld_decompose_lo_88` (concl th)) &&
        not(free_in `mld_decompose_hi_88` (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    VAL_INT64_TAC (parse_term idx) THEN
    ASSUME_TAC(REWRITE_RULE[ARITH_RULE (parse_term(Printf.sprintf "%d + 4 * i = 4 * (%s) + %d" wb idx wd))]
      (ASSUME (parse_term(Printf.sprintf "read(memory :> bytes32(word_add rsp0 (word(%d + 4 * i)))) s0 = (x:num->int32) i" wb)))) THEN
    alias w1d w1b THEN alias wd wb THEN
    X86_STEPS_TAC exec (1--13) THEN
    REG32_LANE_TAC `RSI` `(x:num->int32) i` `mld_decompose_hi_88` [mld_decompose_hi_88; mld_ct_sel] THEN
    X86_STEPS_TAC exec (14--26) THEN
    DECOMP_LO_LANE_TAC `RCX` `(x:num->int32) i` THEN
    X86_STEPS_TAC exec (27--30) THEN
    ADDR_LINEAR_BASES_TAC [wb; w1b] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ONE_OUTPUT_SPLIT] THEN
    LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
    TRY(REWRITE_TAC[WORD_ZX_ZX_32_64_32] THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    FULL_EXIT0_TAC];;

let PROVE_DECOMP88 fn loop exit wd w1d r0 =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(DECOMP88_STMT fn loop exit wd w1d r0, DECOMP88_TAC exec fn loop exit wd w1d r0);;

(* ------------------------------------------------------------------------- *)
(* mld_polyw1_pack_88 of the polynomial x at c to the 192 bytes at rsp0 + ob *)
(* (ob = d0 + r0): 64 iterations, each turning 4 coefficients (at RCX - 12,  *)
(* ..., RCX) into 3 bytes, stored at [rsp + rax + d0], [.. + d0 + 1] and     *)
(* [.. + d0 + 2], RAX being r0 + 3 i and RCX c + 12 + 16 i. The loads at     *)
(* negative displacements from RCX have the aliases of PACKW1_ALIASES.       *)
(* ------------------------------------------------------------------------- *)

let W1PACKS_ALIASES =
  ["word_add (word_add c (word (16 * i + 12))) (word 18446744073709551604):int64 = word_add c (word (16 * i))";
   "word_add (word_add c (word (16 * i + 12))) (word 18446744073709551608):int64 = word_add c (word (16 * i + 4))";
   "word_add (word_add c (word (16 * i + 12))) (word 18446744073709551612):int64 = word_add c (word (16 * i + 8))"];;

let W1PACKS_STMT fn loop exit d0 r0 =
  let ob = d0 + r0 in
  parse_term(Printf.sprintf
  "exists f_events.
  forall e c rsp0 pc (x:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    ALL (nonoverlapping (word_add rsp0 (word %d),192)) [(c,1024); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word %d /\\
              read RCX s = word_add c (word 12) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add c (word (4*i)))) s = x i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word %d /\\
              read RCX s = word_add c (word 1036) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add c (word (4*i)))) s = x i) /\\
              (!j. j < 192 ==> read (memory :> bytes8 (word_add rsp0 (word (%d + j)))) s =
                               mld_polyw1_pack_88 x j) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events c rsp0 pc /\\
                 memaccess_inbounds e2 [c,1024; word_add rsp0 (word %d),192]
                                       [word_add rsp0 (word %d),192]))
         (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; RDI] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(word_add rsp0 (word %d),192)])"
  ob image_mc fn loop r0 fn exit (r0 + 192) ob ob ob ob);;

let W1PACKS_TAC exec fn loop exit d0 r0 =
  let ob = d0 + r0 in
  CONCRETIZE_F_EVENTS_TAC
   `\(c:int64) (rsp0:int64) (pc:num).
      APPEND (f_ev_epil c rsp0 pc)
       (APPEND (ENUMERATEL 64 (\i. f_ev_loop c rsp0 pc i)) (f_ev_prol c rsp0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `c:int64`; `rsp0:int64`; `pc:num`; `x:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `64` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read RSP s = rsp0 /\\
          read RAX s = word (%d + 3 * i) /\\
          read RCX s = word_add c (word (16 * i + 12)) /\\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add c (word(4 * j)))) s = x j) /\\
          (!j. j < 3 * i
               ==> read(memory :> bytes8(word_add rsp0 (word(%d + j)))) s = mld_polyw1_pack_88 x j)"
    r0 ob)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    CHUNK_INPUT_TAC `x:num->int32` 4 THEN
    INPUT_ALT_ADDR_TAC `c:int64` THEN
    VAL_INT64_TAC (parse_term(Printf.sprintf "%d + 3 * i" r0)) THEN
    ALIAS_ASSUME_TAC W1PACKS_ALIASES THEN
    X86_STEPS_TAC exec (1--20) THEN
    CHUNK_FULL_FINAL3_TAC ob
      [ARITH_RULE `3 * (i + 1) = 3 * i + 3`; ARITH_RULE `16 * (i + 1) = 16 * i + 16`;
       ARITH_RULE (parse_term(Printf.sprintf "%d + 3 * (i + 1) = %d + 3 * i + 3" r0 r0))]
      ALL_TAC mld_polyw1_pack_88 `x:num->int32`;
    FULL_EXIT0_TAC];;

let PROVE_W1PACKS fn loop exit d0 r0 =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(W1PACKS_STMT fn loop exit d0 r0, W1PACKS_TAC exec fn loop exit d0 r0);;

(* ------------------------------------------------------------------------- *)
(* mld_poly_chknorm of the polynomial x at p + d with the constant bound bnd *)
(* (p the value of the register reg, RSP or RBX): 256 iterations of one      *)
(* coefficient, addressed as [reg + rcx * 4 + d], RCX being i; the mask of   *)
(* (bnd - 1) - |x i| < 0 is ORed into EAX, which starts at 0. The absolute   *)
(* value is selected as in MLD_CT_ABS_SELECT of chknorm_tools.ml.            *)
(* ------------------------------------------------------------------------- *)

let CHK_ABS_SELECT = prove
 (`!y:int32. mld_ct_abs y =
             word_xor (word_and (word_xor (word_neg y) y) (word_ishr y 31)) y`,
  REWRITE_TAC[mld_ct_abs; GSYM MSB_IVAL; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN BITBLAST_TAC);;

let CHK_OR_ONES = prove
 (`!y:int32. word_or (word 4294967295) y = word 4294967295`,
  BITBLAST_TAC);;

let CHK_EXISTS_LT_SUC = prove
 (`!P i. (?j. j < i + 1 /\ P j) <=> (?j. j < i /\ P j) \/ P i`,
  REWRITE_TAC[ARITH_RULE `j < i + 1 <=> j < i \/ j = i`] THEN MESON_TAC[]);;

let CHK_ZX_USHR_SX_31 = prove
 (`!x:int32. word_zx(word_ushr (word_sx x:int64) 31):int32 = word_ishr x 31`,
  BITBLAST_TAC);;

let CHKNORM_STMT fn loop exit reg d bnd =
  let off = if d = 0 then "4*i" else Printf.sprintf "%d + 4*i" d in
  let rb = if d = 0 then "p" else Printf.sprintf "word_add p (word %d)" d in
  parse_term(Printf.sprintf
  "exists f_events.
  forall e p pc (x:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read %s s = p /\\ read RCX s = word 0 /\\ read RAX s = word 0 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add p (word (%s)))) s = x i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read %s s = p /\\ read RCX s = word 256 /\\
              read RAX s = word_zx (mld_poly_chknorm x (word %d)) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events p pc /\\
                 memaccess_inbounds e2 [%s,1024] []))
         (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; RDI] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events])"
  image_mc fn loop reg off fn exit reg bnd rb);;

let CHKNORM_TAC exec fn loop exit reg d bnd =
  let offj = if d = 0 then "4 * j" else Printf.sprintf "%d + 4 * j" d
  and offi = if d = 0 then "4 * i" else Printf.sprintf "%d + 4 * i" d
  and simi = if d = 0 then "4 * i" else Printf.sprintf "4 * i + %d" d in
  let ex = parse_term(Printf.sprintf
    "?j. j < i /\\ ival(word_sub (word %d:int32) (mld_ct_abs((x:num->int32) j))) < &0" (bnd - 1)) in
  CONCRETIZE_F_EVENTS_TAC
   `\(p:int64) (pc:num).
      APPEND (f_ev_epil p pc)
       (APPEND (ENUMERATEL 256 (\i. f_ev_loop p pc i)) (f_ev_prol p pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `p:int64`; `pc:num`; `x:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read %s s = p /\\ read RCX s = word i /\\
          read RAX s = word_zx(if %s then word 4294967295 else word 0:int32) /\\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add p (word(%s)))) s = x j)"
    reg (string_of_term ex) offj)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONJUNCT1 LT; WORD_ZX_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) && free_in `x:num->int32` (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    VAL_INT64_TAC `i:num` THEN
    (if d = 0 then ALL_TAC else
     ASSUME_TAC(REWRITE_RULE[ARITH_RULE (parse_term(Printf.sprintf "%s = %s" offi simi))]
      (ASSUME (parse_term(Printf.sprintf "read(memory :> bytes32(word_add p (word(%s)))) s0 = (x:num->int32) i" offi))))) THEN
    X86_STEPS_TAC exec (1--16) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(W(fun (asl,w) ->
          if can (find_term (fun t -> is_const t && name_of t = "mld_ct_abs")) w
          then NO_TAC else CONV_TAC WORD_RULE THEN NO_TAC)) THEN
    TRY(REWRITE_TAC[CHK_EXISTS_LT_SUC] THEN ASM_REWRITE_TAC[] THEN
        SPEC_TAC(ex,`q:bool`) THEN GEN_TAC THEN ASM_CASES_TAC `q:bool` THEN
        ASM_REWRITE_TAC[] THENL
         [REWRITE_TAC[WORD_ZX_ZX_32_64_32; WORD_ZX_SX_32_64_32;
                      CHK_ZX_USHR_SX_31; CHK_OR_ONES];
          REWRITE_TAC[WORD_ZX_ZX_32_64_32; WORD_ZX_SX_32_64_32;
                      CHK_ZX_USHR_SX_31] THEN
          REWRITE_TAC[WORD_OR_0; WORD_ISHR_31_COND; CHK_ABS_SELECT]] THEN
        NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[mld_poly_chknorm] THEN
    CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
    REPEAT CONJ_TAC THEN
    TRY(REFL_TAC THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let PROVE_CHKNORM fn loop exit reg d bnd =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(CHKNORM_STMT fn loop exit reg d bnd, CHKNORM_TAC exec fn loop exit reg d bnd);;

(* ------------------------------------------------------------------------- *)
(* Facts about input bytes for a loop that reads them as [rsp + rax + d],    *)
(* RAX being r0 + s i: from the fact that byte j of b is at rsp0 + ib + j,   *)
(* the facts about the bytes s i + k, k < s, at the simulator's addresses    *)
(* word_add rsp0 (word (1 * (r0 + s * i) + (d + k))) with d = ib - r0.       *)
(* ------------------------------------------------------------------------- *)

let IDX_BYTE_FACTS_TAC (b:term) n ib r0 s =
  let d = ib - r0 in
  MAP_EVERY (fun k ->
    let bk = if k = 0 then Printf.sprintf "%d * i" s else Printf.sprintf "%d * i + %d" s k in
    let ix = idx_expr r0 s in
    let t = parse_term(Printf.sprintf
      "read (memory :> bytes8 (word_add rsp0 (word (1 * (%s) + %d)))) s0 = %s (%s)"
      ix (d + k) (fst(dest_var b)) bk) in
    SUBGOAL_THEN t ASSUME_TAC THENL
     [SUBGOAL_THEN (parse_term(Printf.sprintf
        "1 * (%s) + %d = %d + (%s)" ix (d + k) ib bk))
        SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(fun th ->
        if is_forall(concl th) && free_in b (concl th) then
          MATCH_MP_TAC th THEN ASSUME_TAC th else NO_TAC) THEN
      ASM_ARITH_TAC;
      ALL_TAC]) (0--(n-1));;

(* ------------------------------------------------------------------------- *)
(* mld_polyz_unpack_c with gamma1 = 2^17 as inlined into the sampling of y:  *)
(* 9 bytes of the input b (at rsp0 + ib, read as [rsp + rax + ib - 8] etc., *)
(* RAX being 8 + 9 i) become 4 coefficients of 32 bits, stored at RCX - 12, *)
(* ..., RCX, RCX being c + 12 + 16 i: 64 iterations.                         *)
(* ------------------------------------------------------------------------- *)

let UNPACKZ17B_STMT fn loop exit ib =
  parse_term(Printf.sprintf
  "exists f_events.
  forall e c rsp0 pc (b:num->byte).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    ALL (nonoverlapping (c,1024))
        [(word_add rsp0 (word %d),576); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word 8 /\\
              read RCX s = word_add c (word 12) /\\
              (!j. j < 576 ==> read(memory :> bytes8(word_add rsp0 (word (%d + j)))) s = b j) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word 584 /\\
              read RCX s = word_add c (word 1036) /\\
              (!j. j < 576 ==> read(memory :> bytes8(word_add rsp0 (word (%d + j)))) s = b j) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add c (word (4*i)))) s =
                               mld_polyz_unpack_17 b i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events c rsp0 pc /\\
                 memaccess_inbounds e2 [word_add rsp0 (word %d),576; c,1024] [c,1024]))
         (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; RDI; R8; R9] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(c,1024)])"
  ib image_mc fn loop ib fn exit ib ib);;

let UNPACKZ17B_TAC exec fn loop exit ib =
  CONCRETIZE_F_EVENTS_TAC
   `\(c:int64) (rsp0:int64) (pc:num).
      APPEND (f_ev_epil c rsp0 pc)
       (APPEND (ENUMERATEL 64 (\i. f_ev_loop c rsp0 pc i)) (f_ev_prol c rsp0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `c:int64`; `rsp0:int64`; `pc:num`; `b:num->byte`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `64` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read RSP s = rsp0 /\\
          read RAX s = word (8 + 9 * i) /\\
          read RCX s = word_add c (word (16 * i + 12)) /\\
          (!j. j < 576
               ==> read(memory :> bytes8(word_add rsp0 (word (%d + j)))) s = b j) /\\
          (!j. j < 4 * i
               ==> read(memory :> bytes32(word_add c (word(4 * j)))) s =
                   mld_polyz_unpack_17 b j)" ib)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0; ADD_CLAUSES] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    IDX_BYTE_FACTS_TAC `b:num->byte` 9 ib 8 9 THEN
    VAL_INT64_TAC `8 + 9 * i` THEN
    MP_TAC(READ_MEMORY_MERGE_CONV 1 (parse_term(Printf.sprintf
      "read(memory :> bytes16(word_add rsp0 (word (1 * (8 + 9 * i) + %d)))) s0" (ib - 8)))) THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ALIAS_ASSUME_TAC W1PACKS_ALIASES THEN
    X86_STEPS_TAC exec (1--46) THEN
    CHUNK_FULL_FINAL_ARS_TAC
      [ARITH_RULE `8 + 9 * (i + 1) = 8 + 9 * i + 9`; ARITH_RULE `16 * (i + 1) = 16 * i + 16`]
      mld_polyz_unpack_17 `b:num->byte`;
    FULL_EXIT0_TAC];;

let PROVE_UNPACKZ17B fn loop exit ib =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(UNPACKZ17B_STMT fn loop exit ib, UNPACKZ17B_TAC exec fn loop exit ib);;

(* ------------------------------------------------------------------------- *)
(* mld_polyeta_unpack with eta = 2 (ML-DSA-44, ML-DSA-87) as inlined into the *)
(* attempt: 3 bytes of the input b at a, read at RAX - 2, RAX - 1 and RAX,   *)
(* RAX being a + 2 + 3 i, become 8 coefficients 2 - t, stored (each but the  *)
(* last twice) at [rsp + rcx + ob + 4 k], RCX being 32 i: 32 iterations. The *)
(* temporaries other than RDX, RSI, RDI and R8 to R11 are in regs (RBX and   *)
(* R14, or R14 and R15).                                                     *)
(* ------------------------------------------------------------------------- *)

let ETA2U_ALIASES =
  ["word_add (word_add a (word (3 * i + 2))) (word 18446744073709551614):int64 = word_add a (word (3 * i))";
   "word_add (word_add a (word (3 * i + 2))) (word 18446744073709551615):int64 = word_add a (word (3 * i + 1))"];;

let ETA2U_STMT fn loop exit ob regs =
  parse_term(Printf.sprintf
  "exists f_events.
  forall e a rsp0 pc (b:num->byte).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    ALL (nonoverlapping (word_add rsp0 (word %d),1024))
        [(a,96); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word_add a (word 2) /\\
              read RCX s = word 0 /\\
              (!j. j < 96 ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word_add a (word 98) /\\
              read RCX s = word 1024 /\\
              (!j. j < 96 ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s =
                               mld_polyeta_unpack_2 b i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events a rsp0 pc /\\
                 memaccess_inbounds e2 [a,96; word_add rsp0 (word %d),1024]
                                       [word_add rsp0 (word %d),1024]))
         (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11; %s] ,,
          MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(word_add rsp0 (word %d),1024)])"
  ob image_mc fn loop fn exit ob ob ob regs ob);;

let ETA2U_TAC exec fn loop exit ob =
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (rsp0:int64) (pc:num).
      APPEND (f_ev_epil a rsp0 pc)
       (APPEND (ENUMERATEL 32 (\i. f_ev_loop a rsp0 pc i)) (f_ev_prol a rsp0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `rsp0:int64`; `pc:num`; `b:num->byte`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read RSP s = rsp0 /\\
          read RAX s = word_add a (word (3 * i + 2)) /\\
          read RCX s = word (32 * i) /\\
          (!j. j < 96
               ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\\
          (!j. j < 8 * i
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s =
                   mld_polyeta_unpack_2 b j)" ob)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0; ADD_CLAUSES] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    CHUNK_INPUT_TAC `b:num->byte` 3 THEN
    INPUT_ALT_ADDR_TAC `a:int64` THEN
    ALIAS_ASSUME_TAC ETA2U_ALIASES THEN
    VAL_INT64_TAC `32 * i` THEN
    X86_STEPS_TAC exec (1--61) THEN
    CHUNK_FULL_FINAL3_TAC ob
      [ARITH_RULE `3 * (i + 1) + 2 = 3 * i + 5`; ARITH_RULE `32 * (i + 1) = 32 * i + 32`]
      ALL_TAC mld_polyeta_unpack_2 `b:num->byte`;
    FULL_EXIT0_TAC];;

let PROVE_ETA2U fn loop exit ob regs =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(ETA2U_STMT fn loop exit ob regs, ETA2U_TAC exec fn loop exit ob);;

(* ------------------------------------------------------------------------- *)
(* The squeezing of the 5 blocks (680 bytes) of SHAKE256 in the sampling of  *)
(* y (mldsa_shake256_squeeze inlined into mld_poly_uniform_gamma1), as       *)
(* x86-A's PU_B of inline_pu.ml for poly_uniform: from the test of the       *)
(* position at the head (pos = 136, so the state is permuted before each     *)
(* block), each iteration permutes the state at rsp0 + st with              *)
(* mldsa_keccakf1600_permute and copies its first 136 bytes with memcpy to   *)
(* rsp0 + buf + 136 i. The position, the number of bytes left, the offset    *)
(* in the output, the length of the copy and the pointer to the state are in *)
(* the registers pos, rem, off, len and sp (callee-saved, as the calls       *)
(* preserve them); the callees use the 296 bytes of stack below rsp0. The    *)
(* code of the loop starts at the label lo, below the head.                  *)
(* ------------------------------------------------------------------------- *)

type sqz_cfg =
 { sq_fn : string; sq_lo : string; sq_head : string; sq_exit : string;
   sq_pos : string; sq_rem : string; sq_off : string; sq_len : string;
   sq_sp : string; sq_st : int; sq_buf : int };;

let sqz_sub c s =
  subst_tokens
   ["@MC@",image_mc; "@FN@",c.sq_fn; "@HEAD@",c.sq_head; "@EXIT@",c.sq_exit;
    "@POS@",c.sq_pos; "@REM@",c.sq_rem; "@OFF@",c.sq_off; "@LEN@",c.sq_len;
    "@SP@",c.sq_sp; "@ST@",string_of_int c.sq_st; "@BUF@",string_of_int c.sq_buf;
    "@FRN@",string_of_int (296 + c.sq_buf + 680)] s;;

let SQZ_STMT c = parse_term(sqz_sub c
 "!mc ea el ev.
    memcpy_full_contract mc ea el ev
    ==> exists f_events.
      forall e (S:1600 word) (rsp0:int64) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        ALLPAIRS nonoverlapping [(word_sub rsp0 (word 296),@FRN@)]
          [(word pc,libmldsa_size); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures x86
          (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + @FN@_@HEAD@) /\\
                read RSP s = rsp0 /\\
                read @POS@ s = word 136 /\\ read @REM@ s = word 680 /\\
                read @OFF@ s = word 0 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes (word_add rsp0 (word @ST@),200)) s = val(S:1600 word) /\\
                read events s = e)
          (\\s. read RIP s = word (pc + @FN@_@EXIT@) /\\
                read RSP s = rsp0 /\\
                read @POS@ s = word 136 /\\ read @REM@ s = word 0 /\\
                read @OFF@ s = word 680 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes (word_add rsp0 (word @ST@),200)) s =
                  val(keccak_squeeze 5 S) /\\
                (!j. j < 680
                     ==> read (memory :> bytes8 (word_add rsp0 (word (@BUF@ + j)))) s =
                         mld_keccak_squeeze_byte 136 S 136 j) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events rsp0 mc pc /\\
                   memaccess_inbounds e2
                    [word_sub rsp0 (word 296),@FRN@; word(pc + got_memcpy),8; ea,el;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192]
                    [word_sub rsp0 (word 296),296; word_add rsp0 (word @ST@),200;
                     word_add rsp0 (word @BUF@),680]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [RSP] ,, MAYCHANGE [@POS@; @REM@; @OFF@; @LEN@; @SP@] ,,
           MAYCHANGE [memory :> bytes(word_sub rsp0 (word 296),296);
                      memory :> bytes(word_add rsp0 (word @ST@),200);
                      memory :> bytes(word_add rsp0 (word @BUF@),680)])");;

let SQZ_INV c = parse_term(sqz_sub c
 "\\i s. read RSP s = rsp0 /\\ read @POS@ s = word 136 /\\
        read @REM@ s = word (680 - 136 * i) /\\ read @OFF@ s = word (136 * i) /\\
        (read DF s <=> false) /\\
        read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
        read (memory :> bytes(ea,el)) s = ev /\\
        read (memory :> bytes (word_add rsp0 (word @ST@),200)) s = val(keccak_squeeze i S) /\\
        read (memory :> bytes(word_add rsp0 (word @BUF@),136 * i)) s =
          nsum {j | j < i} (\\j. 2 EXP (8 * 136 * j) *
                                val(keccak_squeeze (j + 1) S) MOD 2 EXP (8 * 136))");;

let SQZ_ALLOWED = [`rsp0:int64`; `mc:int64`; `pc:num`; `i:num`; `S:1600 word`];;

let SQZ_FIRST136 = prove
 (`!(a:int64) (X:1600 word) s:x86state.
     read (memory :> wbytes a) s = X
     ==> read (memory :> bytes(a,136)) s = val X MOD 2 EXP (8 * 136)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; GSYM READ_BYTES_MOD] THEN
  REWRITE_TAC[READ_BYTES_MOD] THEN CONV_TAC NUM_REDUCE_CONV);;

let SQZ_SQ_SUC = prove
 (`!(S:1600 word) i. keccak_f1600 (keccak_squeeze i S) = keccak_squeeze (i + 1) S`,
  REWRITE_TAC[GSYM ADD1; keccak_squeeze]);;

let SQZ_NSUM_SUC = prove
 (`!(f:num->num) i. nsum {j | j < i + 1} f = nsum {j | j < i} f + f i`,
  REWRITE_TAC[GSYM ADD1; NSUM_CLAUSES_NUMSEG_LT]);;

let SQZ_EXTBLK = prove
 (`!(rsp0:int64) buf i (S:1600 word) s:x86state.
     read (memory :> bytes(word_add rsp0 (word buf),136 * i)) s =
       nsum {j | j < i} (\j. 2 EXP (8 * 136 * j) * val(keccak_squeeze (j + 1) S) MOD 2 EXP (8 * 136)) /\
     read (memory :> bytes(word_add rsp0 (word (136 * i + buf)),136)) s =
       val(keccak_squeeze (i + 1) S) MOD 2 EXP (8 * 136)
     ==> read (memory :> bytes(word_add rsp0 (word buf),136 * (i + 1))) s =
       nsum {j | j < i + 1} (\j. 2 EXP (8 * 136 * j) * val(keccak_squeeze (j + 1) S) MOD 2 EXP (8 * 136))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SQZ_NSUM_SUC; READ_COMPONENT_COMPOSE; ARITH_RULE `136 * (i + 1) = 136 * i + 136`;
              READ_BYTES_COMBINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  SUBGOAL_THEN `word_add (word_add rsp0 (word buf)) (word (136 * i)):int64 =
                word_add rsp0 (word (136 * i + buf))` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN REWRITE_TAC[ARITH_RULE `8 * 136 * i = 8 * (136 * i)`]);;

let SQZ_ARITH = prove
 (`!i. i < 5
       ==> word_sub (word (680 - 136 * i)) (word 136):int64 = word (680 - 136 * (i + 1)) /\
           (val(word_sub (word (680 - 136 * i)) (word 136):int64) = 0 <=> ~(i + 1 < 5)) /\
           word_add (word (136 * i)) (word 136):int64 = word (136 * (i + 1))`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let SQZ_CSEL = prove
 (`!i. i < 5 ==> (if val(word(680 - 136 * i):int64) < 136 then word(680 - 136 * i):int64 else word 136) = word 136`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let SQZ_VAL136 = prove
 (`!i. i < 5 ==> val(word(136 * i):int64) = 136 * i`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
  UNDISCH_TAC `i < 5` THEN ARITH_TAC);;

let SQZ_RENAME_E2 = CONV_RULE(DEPTH_CONV(fun tm ->
  if is_exists tm && name_of(fst(dest_exists tm)) = "e2"
  then ALPHA_CONV (mk_var("ec",type_of(fst(dest_exists tm)))) tm
  else failwith "SQZ_RENAME_E2"));;

let SQZ_ADDR_CONV =
  let wadd = `word_add:int64->int64->int64` and wd = `word:num->int64` in
  fun tm ->
   match tm with
     Comb(Comb(Const("word_add",_),Comb(Comb(Const("word_add",_),x),Comb(Const("word",_),a))),Comb(Const("word",_),b)) ->
         let r = mk_comb(mk_comb(`(+):num->num->num`,a),b) in
         prove(mk_eq(tm,mk_comb(mk_comb(wadd,x),mk_comb(wd,r))), CONV_TAC WORD_RULE)
   | _ -> failwith "SQZ_ADDR_CONV";;

let SQZ_NORM_TAC =
  let cv = DEPTH_CONV(SQZ_ADDR_CONV ORELSEC NUM_ADD_CONV) THENC REWRITE_CONV[WORD_ADD_0] in
  RULE_ASSUM_TAC(CONV_RULE cv) THEN TRY(CONV_TAC cv);;

let SQZ_LEFTASSOC_CONV = TRY_CONV(CONS_TO_APPEND_CONV) THENC REWRITE_CONV[APPEND_ASSOC];;

let SQZ_E2_CORE allowed =
  CONV_TAC(LAND_CONV SQZ_LEFTASSOC_CONV) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SAFE_UNIFY_REFL_TAC allowed (ref ["f_events_callee"; "f_ev_"]);;

let SQZ_E2_TAC allowed =
  (CONJ_TAC THENL [CONV_TAC WORD_RULE; SQZ_E2_CORE allowed]) ORELSE SQZ_E2_CORE allowed;;

let SQZ_LIBC_CALL_TAC name execth ilist vars n =
  REMOVE_THEN name (fun th ->
    LIBC_CONTRACT_SIM_TAC ~is_safety_thm:true execth th ilist n THENL
     [(FULL_EXISTS_E2_TAC (ref vars) ORELSE SQZ_E2_TAC (ref vars)); LABEL_TAC name th]);;

(* the addresses from the bottom fb = rsp0 - 296 of the region, so that the
   containment checks of the regions of the callees below rsp0 succeed *)
let SQZ_FB_NORM_TAC =
  let sub = WORD_RULE `word_sub (word_sub (x:int64) (word a)) (word b) =
                       word_sub x (word (a + b))` in
  let norm = REPEATC(CHANGED_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) in
  RULE_ASSUM_TAC(CONV_RULE(REWRITE_CONV[sub] THENC DEPTH_CONV NUM_ADD_CONV)) THEN
  REWRITE_TAC[sub] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  ABBREV_TAC `fb_sq = word_sub rsp0 (word 296):int64` THEN
  SUBGOAL_THEN `rsp0 = word_add fb_sq (word 296):int64` SUBST_ALL_TAC THENL
   [EXPAND_TAC "fb_sq" THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  RULE_ASSUM_TAC(CONV_RULE norm) THEN CONV_TAC norm;;

(* the memaccess facts of the callees with their event lists expanded, so that
   DISCHARGE_MEMACCESS_INBOUNDS_TAC finds them after the definitions of the
   event variables of the callees have been used up *)
let EXPAND_CALLEE_MEMACCESS_TAC =
  W(fun (asl,w) ->
    let defs = mapfilter (fun (_,th) ->
      let c = concl th in
      if is_eq c && is_var(lhs c) && type_of(lhs c) = `:(uarch_event)list` &&
         String.length (fst(dest_var(lhs c))) > 2 &&
         String.sub (fst(dest_var(lhs c))) 0 2 = "e2" &&
         fst(dest_var(lhs c)) <> "e2"
      then th else failwith "") asl in
    if defs = [] then ALL_TAC else
    RULE_ASSUM_TAC(fun th ->
      let c = concl th in
      if is_comb c && (try name_of(fst(strip_comb c)) = "memaccess_inbounds" with _ -> false)
      then REWRITE_RULE defs th else th));;

let SQZ_MAYCHANGE_TAC =
  W(fun (asl,w) -> if maychange_term w then ALL_TAC else NO_TAC) THEN
  SQZ_FB_NORM_TAC THEN
  FIRST_X_ASSUM(fun th -> if maychange_term (concl th) && not(is_forall(concl th))
                          then MP_TAC th else NO_TAC) THEN
  DISCH_TAC THEN MONOTONE_MAYCHANGE_TAC;;

let SQZ_SAFETY_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  (CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN
  SQZ_FB_NORM_TAC THEN
  REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN REPEAT CONJ_TAC THEN DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

let SQZ_TAC c =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [layout (c.sq_fn ^ "_" ^ c.sq_lo), layout (c.sq_fn ^ "_" ^ c.sq_exit);
      layout "plt_memcpy", layout "plt_memcpy" + 16] in
  let wb6 = parse_term(Printf.sprintf
    "read (memory :> wbytes (word_add rsp0 (word %d):int64)) s6:1600 word" c.sq_st) in
  let lbl n = parse_term(Printf.sprintf "pc + %s_%s" c.sq_fn n) in
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memcpy_full_contract] th) "H_MEMCPY") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   (SQZ_RENAME_E2 MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600) "H_PERM" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (mc:int64) (pc:num).
      APPEND (f_ev_epil rsp0 mc pc)
       (APPEND (ENUMERATEL 5 (\i. if i + 1 < 5 then f_ev_c rsp0 mc pc i else f_ev_l rsp0 mc pc i))
               (f_ev_prol rsp0 mc pc)):(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `S:1600 word`; `rsp0:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; ALLPAIRS; PAIRWISE;
              NONOVERLAPPING_CLAUSES; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `5` (lbl c.sq_head) (lbl c.sq_exit) (SQZ_INV c) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; CONJUNCT1 ENUMERATEL; CONJUNCT1 APPEND] THEN
    REPEAT CONJ_TAC THEN
    REWRITE_TAC[keccak_squeeze; NSUM_CLAUSES_NUMSEG_LT; READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
    TRY DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN FULL_INIT_TAC THEN
    X86_STEPS_TAC exec (1--5) THEN SQZ_NORM_TAC THEN
    KECCAK_STATE_WBYTES_TAC `keccak_squeeze i S` THEN
    FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc exec "H_PERM"
     [`read RDI s`; `keccak_squeeze i S`; `pc:num`; `read RSP s`;
      `read (memory :> bytes64 (read RSP s)) s`] SQZ_ALLOWED 6 THEN
    EXPAND_CALLEE_MEMACCESS_TAC THEN RSP_NORM_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[SQZ_SQ_SUC]) THEN SQZ_NORM_TAC THEN
    FIRST_X_ASSUM(fun th ->
      if (try lhs(concl th) = wb6 with _ -> false)
      then ASSUME_TAC(MATCH_MP SQZ_FIRST136 th) THEN ASSUME_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600] th)
      else NO_TAC) THEN
    X86_STEPS_TAC exec (7--16) THEN SQZ_NORM_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `i:num` SQZ_CSEL) (ASSUME `i < 5`)]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `i:num` SQZ_VAL136) (ASSUME `i < 5`); MULT_CLAUSES]) THEN
    SQZ_NORM_TAC THEN
    LIBC_PLT_TAC exec (layout "plt_memcpy") (layout "got_memcpy") 16 THEN
    SQZ_LIBC_CALL_TAC "H_MEMCPY" exec
     [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
      `val(keccak_squeeze (i + 1) S) MOD 2 EXP (8 * 136)`;
      `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`] SQZ_ALLOWED 18 THEN
    EXPAND_CALLEE_MEMACCESS_TAC THEN RSP_NORM_TAC THEN SQZ_NORM_TAC THEN
    X86_STEPS_TAC exec (19--22) THEN SQZ_NORM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `i:num` SQZ_ARITH) (ASSUME `i < 5`)]) THEN
    REWRITE_TAC[MP (SPEC `i:num` SQZ_ARITH) (ASSUME `i < 5`)] THEN SQZ_NORM_TAC THEN
    ASM_CASES_TAC `i + 1 < 5` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    FIRST [MATCH_MP_TAC SQZ_EXTBLK THEN ASM_REWRITE_TAC[];
           SQZ_MAYCHANGE_TAC;
           REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
           ASM_REWRITE_TAC[] THEN SQZ_SAFETY_TAC];
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `136 * 5 = 680`]) THEN
    CONJ_TAC THENL
     [MP_TAC(REWRITE_RULE[ARITH_RULE `136 * 5 = 680`]
        (SPECL [parse_term(Printf.sprintf "word_add rsp0 (word %d):int64" c.sq_buf);
                `136`; `5`; `S:1600 word`; `s0:x86state`] MLD_SQUEEZE_BLOCKS_BYTES8)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[ARITH_RULE `0 < 136`]; ALL_TAC] THEN
      REWRITE_TAC[WORD_ADD_ASSOC_CONSTS; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      DISCH_THEN ACCEPT_TAC;
      ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let PROVE_SQZ c = prove(SQZ_STMT c, SQZ_TAC c);;

(* ------------------------------------------------------------------------- *)
(* The start of the sampling of a polynomial of y (mld_poly_uniform_gamma1   *)
(* with mldsa_shake256_init, _absorb and _finalize inlined), 49 instructions *)
(* from the load of the pointer to rho'' (slot rsp0 + 128) and of kappa      *)
(* (16 bits at rsp0 + 136): the 66 bytes rho'' || kappa + j (j in the        *)
(* register jreg, saved at rsp0 + jslot) copied to rsp0 + inb, the state at  *)
(* rsp0 + st zeroed, the input XORed into it with the padding bytes 0x1F and *)
(* 0x80, the position 136 stored after the state, and the registers pos,     *)
(* rem and off of the squeezing set to 136, 680 and 0. The state is then     *)
(* mld_keccak_absorb_once 136 0x1F 66 M of mld_shake256_stream, assembled    *)
(* from its pieces as x86-A's PU_A of inline_pu.ml does it.                  *)
(* ------------------------------------------------------------------------- *)

type g1a_cfg =
 { ga_fn : string; ga_start : string; ga_end : string; ga_jreg : string;
   ga_jsave : string; ga_jslot : int; ga_inb : int; ga_st : int;
   ga_pos : string; ga_rem : string; ga_off : string };;

let g1a_sub c s =
  subst_tokens
   ["@MC@",image_mc; "@FN@",c.ga_fn; "@START@",c.ga_start; "@END@",c.ga_end;
    "@JREG@",c.ga_jreg; "@JSAVE@",c.ga_jsave; "@JSLOT@",string_of_int c.ga_jslot;
    "@JLEN@",(if c.ga_jsave = "bytes32" then "4" else "8");
    "@JVAL@",(if c.ga_jsave = "bytes32" then "word j:int32" else "word j:int64");
    "@IN@",string_of_int c.ga_inb; "@ST@",string_of_int c.ga_st;
    "@POS@",c.ga_pos; "@REM@",c.ga_rem; "@OFF@",c.ga_off] s;;

let G1A_STMT c = parse_term(g1a_sub c
 "exists f_events.
    forall e (rsp0:int64) (rp:int64) (R:num) kap j pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 16 rsp0 /\\ j < 65536 /\\
      ALL (nonoverlapping (rp,64))
        [(word_add rsp0 (word @ST@),204); (word_add rsp0 (word @IN@),66);
         (word_add rsp0 (word @JSLOT@),@JLEN@)] /\\
      ALL (nonoverlapping (word pc,libmldsa_size))
        [(word_add rsp0 (word @ST@),204); (word_add rsp0 (word @IN@),66);
         (word_add rsp0 (word @JSLOT@),@JLEN@)]
      ==> ensures x86
           (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + @FN@_@START@) /\\
                read RSP s = rsp0 /\\ read @JREG@ s = word j /\\
                read (memory :> bytes64 (word_add rsp0 (word 128))) s = rp /\\
                read (memory :> bytes16 (word_add rsp0 (word 136))) s = word kap /\\
                read (memory :> bytes(rp,64)) s = R /\\
                read events s = e)
           (\\s. read RIP s = word (pc + @FN@_@END@) /\\
                read RSP s = rsp0 /\\
                read @POS@ s = word 136 /\\ read @REM@ s = word 680 /\\
                read @OFF@ s = word 0 /\\
                read (memory :> @JSAVE@ (word_add rsp0 (word @JSLOT@))) s = @JVAL@ /\\
                read (memory :> bytes(word_add rsp0 (word @ST@),200)) s =
                  val(mld_keccak_absorb_once 136 0x1F 66
                       (R + 2 EXP 512 * val(word(kap + j):int16))) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events rsp0 rp pc /\\
                   memaccess_inbounds e2
                    [rp,64; word_add rsp0 (word 128),10; word_add rsp0 (word @ST@),204;
                     word_add rsp0 (word @IN@),80]
                    [word_add rsp0 (word @ST@),204; word_add rsp0 (word @IN@),66;
                     word_add rsp0 (word @JSLOT@),@JLEN@]))
           (MAYCHANGE [RIP; RAX; RCX; @POS@; @REM@; @OFF@] ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4] ,, MAYCHANGE SOME_FLAGS ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(word_add rsp0 (word @ST@),204);
                       memory :> bytes(word_add rsp0 (word @IN@),66);
                       memory :> bytes(word_add rsp0 (word @JSLOT@),@JLEN@)])");;

(*** The absorbed state of the 66 bytes of rho'' || nonce as a number and a
     word: the input, the padding byte 0x1F after it and 0x80 at byte 135 ***)

let G1A_ABSORB_VAL = prove
 (`!M. M < 2 EXP 528
       ==> val(mld_keccak_absorb_once 136 0x1F 66 M:1600 word) =
           M + 2 EXP 528 * 31 + 2 EXP 1080 * 128`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[MLD_KECCAK_ABSORB_ONCE] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  REWRITE_TAC[keccak_absorb; WORD_XOR_0; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  SIMP_TAC[MLD_KECCAK_PAD_SHORT; ARITH_RULE `66 + 2 <= 136`; ARITH_RULE `31 < 256`] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1] THEN
  SUBGOAL_THEN `(M + 2 EXP (8 * 66) * (31 + 2 EXP (8 * (136 - 66 - 1)) * 128)) =
                M + 2 EXP 528 * 31 + 2 EXP 1080 * 128` SUBST1_TAC THENL
   [REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM EXP_ADD; ADD_ASSOC] THEN
    CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `(M + 2 EXP 528 * 31 + 2 EXP 1080 * 128) < 2 EXP 1088` ASSUME_TAC THENL
   [UNDISCH_TAC `M < 2 EXP 528` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `8 * 136 = 1088`] THEN ASM_SIMP_TAC[MOD_LT] THEN
  MATCH_MP_TAC MOD_LT THEN FIRST_ASSUM(fun th -> MP_TAC th) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let G1A_S_WORD = prove
 (`!M. M < 2 EXP 528
       ==> mld_keccak_absorb_once 136 0x1F 66 M =
           word_or (word_zx (word M:528 word):1600 word)
                   (word(2 EXP 528 * 31 + 2 EXP 1080 * 128))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  ASM_SIMP_TAC[G1A_ABSORB_VAL] THEN
  SUBGOAL_THEN `(word_zx (word M:528 word):1600 word) || word (2 EXP 528 * 31 + 2 EXP 1080 * 128) =
                word_add (word_zx (word M:528 word):1600 word) (word (2 EXP 528 * 31 + 2 EXP 1080 * 128))`
   SUBST1_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN `M + 2 EXP 528 * 31 + 2 EXP 1080 * 128 < 2 EXP 1600` ASSUME_TAC THENL
   [UNDISCH_TAC `M < 2 EXP 528` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `M < 2 EXP 1600` ASSUME_TAC THENL
   [UNDISCH_TAC `M < 2 EXP 528` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_ZX_GEN; VAL_WORD;
              DIMINDEX_CONV `dimindex(:1600)`; DIMINDEX_CONV `dimindex(:528)`] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `MIN 528 1600 = 528`] THEN
  SUBGOAL_THEN `M MOD 2 EXP 528 = M` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(2 EXP 528 * 31 + 2 EXP 1080 * 128) MOD 2 EXP 1600 =
                2 EXP 528 * 31 + 2 EXP 1080 * 128` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[ADD_ASSOC] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  ASM_REWRITE_TAC[GSYM ADD_ASSOC]);;

(*** rho'' || nonce as a word, and the 128-bit chunks of rho'' ***)

let G1A_M_JOIN = prove
 (`!R (n:int16). R < 2 EXP 512
                 ==> (word (R + 2 EXP 512 * val n):528 word) =
                     word_join n (word R:512 word)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_JOIN; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  MP_TAC(ISPEC `n:int16` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_16] THEN DISCH_TAC THEN
  SUBGOAL_THEN `R MOD 2 EXP 512 = R` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(R + 2 EXP 512 * val(n:int16)) MOD 2 EXP 528 = R + 2 EXP 512 * val n`
   SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `R < 2 EXP 512` THEN
    UNDISCH_TAC `val(n:int16) < 2 EXP 16` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(2 EXP 512 * val(n:int16) + R) MOD 2 EXP 528 = 2 EXP 512 * val n + R`
   SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `R < 2 EXP 512` THEN
    UNDISCH_TAC `val(n:int16) < 2 EXP 16` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ARITH_TAC]);;

let G1A_SUBW128 = prove
 (`!R k. R < 2 EXP 512 /\ k < 4
         ==> word((R DIV 2 EXP (128 * k)) MOD 2 EXP 128):int128 =
             word_subword (word R:512 word) (128 * k,128)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; VAL_WORD_SUBWORD; DIMINDEX_128] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  SUBGOAL_THEN `R MOD 2 EXP 512 = R` (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MIN; MOD_MOD_REFL] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_MOD_REFL]);;

(*** The nonce kappa + j as the code computes it in CX (MOVZX of the 16 bits
     of kappa, 16-bit ADD of the low half of jreg), as a 16-bit word ***)

let G1A_NONCE16 = prove
 (`!(a:int16) (j:int64) (h:48 word).
     word (val (word_join h (word (val (word_zx (word_zx a:int32):int64) MOD 65536 +
                                  val j MOD 65536):int16):int64) MOD 65536):int16 =
     word_add a (word_zx j)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; VAL_WORD_ADD; VAL_WORD_ZX_GEN; VAL_WORD_JOIN] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `a:int16` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(a:int16) MOD 4294967296 MOD 18446744073709551616 MOD 65536 = val a`
   SUBST1_TAC THENL
   [ASM_SIMP_TAC[MOD_LT; ARITH_RULE `x < 65536 ==> x < 4294967296`;
                 ARITH_RULE `x < 65536 ==> x < 18446744073709551616`]; ALL_TAC] THEN
  REWRITE_TAC[MOD_MOD_REFL; ARITH_RULE `18446744073709551616 = 65536 * 281474976710656`;
              MOD_MOD] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[MOD_MULT_ADD; MOD_MOD_REFL]);;

let G1A_NONCE16B = prove
 (`!a b. word_add (word a) (word_zx (word b:int64)):int16 = word (a + b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ADD; VAL_WORD_ZX_GEN; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `18446744073709551616 = 65536 * 281474976710656`; MOD_MOD] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[]);;

(*** A 128-bit read whose low 16 bits are known ***)

let G1A_LOW16 = prove
 (`!a:int64 s:x86state (n:int16).
     read (memory :> bytes16 a) s = n
     ==> ?h:112 word. read (memory :> bytes128 a) s = word_join h n`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `word_subword (read (memory :> bytes128 a) s:int128) (16,112):112 word` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);
              el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);
              el 3 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
  CONV_TAC WORD_BLAST);;

(*** The pieces of the state: a fact about the 16 or 1 bytes at an offset,
     with the value given as a subword of the state word S ***)

let G1A_B16 = prove
 (`!a:int64 s:x86state. read (memory :> bytes(a,16)) s = val(read (memory :> bytes128 a) s)`,
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let G1A_PIECE16 = prove
 (`!(S:1600 word) (A:int64) (s:x86state) (V:int128) off.
     read (memory :> bytes128 A) s = V /\ V = word_subword S (8 * off,128)
     ==> read (memory :> bytes(A,16)) s = (val S DIV 2 EXP (8 * off)) MOD 2 EXP 128`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[G1A_B16] THEN
  ASM_REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_CONV `dimindex(:128)`; MIN; LE_REFL] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let G1A_PIECE8 = prove
 (`!(S:1600 word) (A:int64) (s:x86state) (V:byte) off.
     read (memory :> bytes8 A) s = V /\ V = word_subword S (8 * off,8)
     ==> read (memory :> bytes(A,1)) s = (val S DIV 2 EXP (8 * off)) MOD 2 EXP 8`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[READ_MEMORY_BYTES_BYTES8] THEN
  ASM_REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_CONV `dimindex(:8)`; MIN; LE_REFL] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let G1A_EXTEND = prove
 (`!d:int64 j k x s:x86state.
        read (memory :> bytes(d,j)) s = x MOD 2 EXP (8 * j) /\
        read (memory :> bytes(word_add d (word j),k)) s =
        (x DIV 2 EXP (8 * j)) MOD 2 EXP (8 * k)
        ==> read (memory :> bytes(d,j + k)) s = x MOD 2 EXP (8 * (j + k))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; MOD_MULT_MOD] THEN
  ARITH_TAC);;

(*** Byte k of a 128-bit word 0 at a, and the 128-bit chunks as bytes ***)

let G1A_ZBYTE = prove
 (`!(a:int64) k (s:x86state).
     read (memory :> bytes128 a) s = word 0 /\ k < 16
     ==> read (memory :> bytes8 (word_add a (word k))) s = word 0`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[MLD_READ_BYTES128; READ_MEMORY_BYTES_BYTES8] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int128->num`) THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_128; VAL_WORD_0] THEN
  MP_TAC(ISPECL [`a:int64`; `16`; `read memory (s:x86state)`] READ_BYTES_BOUND) THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[MOD_LT] THEN DISCH_THEN(K ALL_TAC) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`a:int64`; `16`; `0`; `k:num`; `1`; `s:x86state`] READ_MEMORY_BYTES_SUB) THEN
  ASM_REWRITE_TAC[DIV_0; MOD_0] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[READ_MEMORY_BYTES_BYTES8; GSYM VAL_EQ; VAL_WORD_0] THEN SIMP_TAC[]);;

(* zero bytes off + k, k in ks, of the zero chunk at rsp0 + off in state sn *)
let G1A_ZBYTES_TAC sn off ks =
  let s = mk_var(sn,`:x86state`) in
  let ch = ASSUME (parse_term(Printf.sprintf
    "read (memory :> bytes128 (word_add rsp0 (word %d))) %s = word 0" off sn)) in
  MAP_EVERY (fun k ->
    let th = MP (SPECL [parse_term(Printf.sprintf "word_add rsp0 (word %d):int64" off);
                        mk_small_numeral k; s] G1A_ZBYTE)
                (CONJ ch (EQT_ELIM(NUM_REDUCE_CONV(mk_binary "<" (mk_small_numeral k,`16`))))) in
    ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV(REWR_CONV(GSYM WORD_ADD_ASSOC) THENC
                 RAND_CONV(REWR_CONV(GSYM WORD_ADD) THENC RAND_CONV NUM_ADD_CONV))) th)) ks;;

(*** The pieces (offset, length) of the 200 bytes of the state at the end ***)

let G1A_PIECES =
  [0,16; 16,16; 32,16; 48,16] @ map (fun j -> j,1) (64--79) @
  [80,16; 96,16; 112,16] @ map (fun j -> j,1) (128--143) @
  [144,16; 160,16] @ map (fun j -> j,1) (176--199);;

let G1A_SW = `word_or (word_zx (word_join (word(kap + j):int16) (word R:512 word):528 word):1600 word)
                      (word(2 EXP 528 * 31 + 2 EXP 1080 * 128))`;;

let G1A_ZX_MOD8 = prove
 (`!y:N word. word (val y MOD 256):byte = word_zx y`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; word_zx; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL]);;

let G1A_ZX_MOD16 = prove
 (`!y:N word. word (val y MOD 65536):int16 = word_zx y`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; word_zx; VAL_WORD; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL]);;

(* the fact bytes(A,len) = (val SW DIV 2 EXP (8 off)) MOD 2 EXP (8 len) of
   the piece at rsp0 + st + off in state sn, the value of its fact (with the
   chunk facts of rho'' as subwords of word R) bit-blasted *)
let G1A_PIECE_THM st asl sn off len =
  let sz,lem = if len = 16 then "bytes128",G1A_PIECE16 else "bytes8",G1A_PIECE8 in
  let ftm = parse_term(Printf.sprintf "read (memory :> %s (word_add rsp0 (word %d))) %s"
                         sz (st + off) sn) in
  let fact = snd(find (fun (_,th) -> let c = concl th in is_eq c && lhs c = ftm) asl) in
  let v = rhs(concl fact) in
  let a = parse_term(Printf.sprintf "word_add rsp0 (word %d):int64" (st + off)) in
  let s = mk_var(sn,`:x86state`) in
  let inst = SPECL [G1A_SW; a; s; v; mk_small_numeral off] lem in
  let eqt = snd(dest_conj(fst(dest_imp(concl inst)))) in
  let eqth = prove(eqt,
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[G1A_ZX_MOD8; G1A_ZX_MOD16] THEN CONV_TAC WORD_BLAST) in
  MP inst (CONJ fact eqth);;

let G1A_NORMC = TRY_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]) THENC
                DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV);;

let G1A_CHAIN_TAC st sn =
  W(fun (asl,w) ->
    let s = mk_var(sn,`:x86state`) in
    let d = parse_term(Printf.sprintf "word_add rsp0 (word %d):int64" st) in
    let x = mk_comb(`val:1600 word->num`,G1A_SW) in
    let cur0 = CONV_RULE G1A_NORMC (prove(
      subst [s,`s:x86state`; x,`x:num`; d,`d:int64`]
       `read (memory :> bytes(d,0)) s = x MOD 2 EXP (8 * 0)`,
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; MULT_CLAUSES; EXP; MOD_1])) in
    let step (cur,j) (off,len) =
      assert (off = j);
      let pth = CONV_RULE G1A_NORMC (G1A_PIECE_THM st asl sn off len) in
      let ext = CONV_RULE G1A_NORMC
        (SPECL [d; mk_small_numeral j; mk_small_numeral len; x; s] G1A_EXTEND) in
      (MP ext (CONJ cur pth), j + len) in
    let fin,n = rev_itlist (fun p st -> step st p) G1A_PIECES (cur0,0) in
    ASSUME_TAC fin);;

let G1A_MODLEMMA = prove
 (`!w:1600 word. val w MOD 2 EXP 1600 = val w`,
  GEN_TAC THEN MATCH_MP_TAC MOD_LT THEN MP_TAC(ISPEC `w:1600 word` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`]);;

(* the 16-bit store at rsp0 + k in state sn as its two bytes *)
let G1A_SPLIT16_TAC sn k =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && lhs c = parse_term(Printf.sprintf
         "read (memory :> bytes16 (word_add rsp0 (word %d))) %s" k sn)
    then STRIP_ASSUME_TAC(CONV_RULE(G1A_NORMC THENC SIMD_SIMPLIFY_CONV [])
                           (CONV_RULE(READ_MEMORY_SPLIT_CONV 1) th))
    else NO_TAC);;

let G1A_ZX_WORD32 = prove
 (`!j. word_zx (word j:int64):int32 = word j`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 64 = 2 EXP 32 * 2 EXP 32`; MOD_MOD]);;

let G1A_TAC c =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [layout (c.ga_fn ^ "_" ^ c.ga_start), layout (c.ga_fn ^ "_" ^ c.ga_end)] in
  let st = c.ga_st and inb = c.ga_inb in
  let al k = parse_term(Printf.sprintf "aligned 16 (word_add rsp0 (word %d):int64)" k) in
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (rp:int64) (pc:num). f_ev_a rsp0 rp pc:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `rp:int64`; `R:num`;
                       `kap:num`; `j:num`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun n -> GHOST_INTRO_TAC (mk_var(Printf.sprintf "ymm%d_init" n,`:int256`))
                       (parse_term(Printf.sprintf "read YMM%d" n))) [0;1;2;3;4] THEN
  FULL_INIT_TAC THEN
  SUBGOAL_THEN `R < 2 EXP 512` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rp:int64`; `64`; `read memory (s0:x86state)`] READ_BYTES_BOUND) THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes(rp,64)) s = R`) (concl th)
    then MP_TAC(MATCH_MP (SPEC `4` MLD_READ_BYTES_CHUNKS)
                 (REWRITE_RULE[ARITH_RULE `64 = 16 * 4`] th))
    else NO_TAC) THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  REWRITE_TAC[EXP; DIV_1; WORD_ADD_0] THEN
  MAP_EVERY (fun k -> REWRITE_TAC[MP (SPECL [`R:num`; mk_small_numeral k] G1A_SUBW128)
      (CONJ (ASSUME `R < 2 EXP 512`) (EQT_ELIM(NUM_REDUCE_CONV(mk_binary "<" (mk_small_numeral k,`4`)))))
      |> CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC REWRITE_CONV[EXP; DIV_1])]) [0;1;2;3] THEN
  STRIP_TAC THEN
  MAP_EVERY (fun k -> SUBGOAL_THEN (al k) ASSUME_TAC THENL
      [MATCH_MP_TAC ALIGNED_WORD_ADD THEN ASM_REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
       CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUMBER_RULE; ALL_TAC])
    (map (fun i -> inb + 16 * i) (0--4) @ map (fun i -> st + 16 * i) (0--11)) THEN
  VERIF_SSE_STEPS_TAC exec (1--26) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[G1A_NONCE16; G1A_NONCE16B]) THEN
  G1A_ZBYTES_TAC "s26" (st + 176) (0--11) THEN
  VERIF_SSE_STEPS_TAC exec (27--27) THEN
  G1A_ZBYTES_TAC "s27" (st + 64) (0--15) THEN
  G1A_ZBYTES_TAC "s27" (st + 128) (0--15) THEN
  G1A_ZBYTES_TAC "s27" (st + 188) (0--11) THEN
  VERIF_SSE_STEPS_TAC exec (28--39) THEN
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && lhs c = parse_term(Printf.sprintf
         "read (memory :> bytes16 (word_add rsp0 (word %d))) s39" (inb + 64))
    then X_CHOOSE_TAC `hjunk:112 word` (MATCH_MP G1A_LOW16 th) else NO_TAC) THEN
  VERIF_SSE_STEPS_TAC exec (40--49) THEN
  G1A_SPLIT16_TAC "s49" (st + 64) THEN
  G1A_CHAIN_TAC st "s49" THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[G1A_ZX_WORD32] THEN REPEAT CONJ_TAC THEN
  TRY(SUBGOAL_THEN `R + 2 EXP 512 * val(word(kap + j):int16) < 2 EXP 528` ASSUME_TAC THENL
       [MP_TAC(ISPEC `word(kap + j):int16` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_16] THEN
        UNDISCH_TAC `R < 2 EXP 512` THEN ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[G1A_S_WORD; G1A_M_JOIN; G1A_MODLEMMA] THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let PROVE_G1A c = prove(G1A_STMT c, G1A_TAC c);;

(* ------------------------------------------------------------------------- *)
(* The end of the sampling of a polynomial of y: the zeroing of the Keccak   *)
(* state (13 aligned stores of 16 bytes from rsp0 + st), of the buffer of    *)
(* 680 bytes at rsp0 + buf (memset, whose address the code keeps in breg)    *)
(* and of the 66 bytes of the input at rsp0 + inb, from the exit of the      *)
(* unpacking loop to the offset fin (22 instructions to the memset and post  *)
(* after it, of which one may be the zeroing of XMM5). Nothing of it is used *)
(* later; the lemma gives the control flow, the events and the frame.        *)
(* ------------------------------------------------------------------------- *)

type zer_cfg =
 { zr_fn : string; zr_start : string; zr_fin : int; zr_st : int; zr_buf : int;
   zr_inb : int; zr_breg : string; zr_post : int };;

let zer_sub c s =
  subst_tokens
   ["@MC@",image_mc; "@FN@",c.zr_fn; "@START@",c.zr_start; "@FIN@",string_of_int c.zr_fin;
    "@ST@",string_of_int c.zr_st; "@BUF@",string_of_int c.zr_buf;
    "@IN@",string_of_int c.zr_inb; "@BREG@",c.zr_breg] s;;

let ZER_STMT c = parse_term(zer_sub c
 "!mf ea el ev.
    memset_full_contract mf ea el ev
    ==> exists f_events.
      forall e (rsp0:int64) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        aligned 16 rsp0 /\\
        ALLPAIRS nonoverlapping
          [(word_sub rsp0 (word 8),8); (word_add rsp0 (word @ST@),208);
           (word_add rsp0 (word @BUF@),680); (word_add rsp0 (word @IN@),66)]
          [(word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)]
        ==> ensures x86
          (\\s. bytes_loaded s (word pc) @MC@ /\\
                read RIP s = word (pc + @FN@_@START@) /\\
                read RSP s = rsp0 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read events s = e)
          (\\s. read RIP s = word (pc + @FN@ + @FIN@) /\\
                read RSP s = rsp0 /\\ read @BREG@ s = word_add rsp0 (word @BUF@) /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events rsp0 mf pc /\\
                   memaccess_inbounds e2
                    [word_sub rsp0 (word 8),8; word_add rsp0 (word @ST@),208;
                     word_add rsp0 (word @BUF@),680; word_add rsp0 (word @IN@),66;
                     word(pc + got_memset),8; ea,el]
                    [word_sub rsp0 (word 8),8; word_add rsp0 (word @ST@),208;
                     word_add rsp0 (word @BUF@),680; word_add rsp0 (word @IN@),66]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [RSP; @BREG@] ,,
           MAYCHANGE [memory :> bytes(word_sub rsp0 (word 8),8);
                      memory :> bytes(word_add rsp0 (word @ST@),208);
                      memory :> bytes(word_add rsp0 (word @BUF@),680);
                      memory :> bytes(word_add rsp0 (word @IN@),66)])");;

let ZER_TAC c =
  let fstart = layout (c.zr_fn ^ "_" ^ c.zr_start) in
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [fstart, layout c.zr_fn + c.zr_fin; layout "plt_memset", layout "plt_memset" + 16] in
  let al k = parse_term(Printf.sprintf "aligned 16 (word_add rsp0 (word %d):int64)" k) in
  let allowed = ref [`rsp0:int64`; `pc:num`; `mf:int64`] in
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] th) "H_MEMSET") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (mf:int64) (pc:num). f_ev_z rsp0 mf pc:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; ALLPAIRS; PAIRWISE;
              NONOVERLAPPING_CLAUSES; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun k -> SUBGOAL_THEN (al k) ASSUME_TAC THENL
      [MATCH_MP_TAC ALIGNED_WORD_ADD THEN ASM_REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
       CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUMBER_RULE; ALL_TAC])
    (map (fun i -> c.zr_st + 16 * i) (0--12) @ map (fun i -> c.zr_inb + 16 * i) (0--3)) THEN
  GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
  FULL_INIT_TAC THEN
  VERIF_SSE_STEPS_TAC exec (1--19) THEN
  SUBGOAL_THEN (parse_term(Printf.sprintf
    "nonoverlapping (word_add rsp0 (word %d):int64,680) (word_sub rsp0 (word 8),8)" c.zr_buf))
   ASSUME_TAC THENL
   [REWRITE_TAC[WORD_RULE `word_sub (x:int64) y = word_add x (word_neg y)`] THEN
    CONV_TAC WORD_REDUCE_CONV THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  X86_STEPS_TAC exec (20--20) THEN
  LIBC_PLT_TAC exec (layout "plt_memset") (layout "got_memset") 20 THEN
  LIBC_FULL_CALL_TAC "H_MEMSET" exec
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
    `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   allowed 22 THEN
  RSP_NORM_TAC THEN
  YMM_GHOST_TAC `s22:x86state` ["YMM0","ymm0_mid"; "YMM5","ymm5_mid"] THEN
  VERIF_SSE_STEPS_TAC exec (23--(22 + c.zr_post)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let PROVE_ZER c = prove(ZER_STMT c, ZER_TAC c);;

(* ------------------------------------------------------------------------- *)
(* mld_polyt0_unpack as inlined into the attempt: 13 bytes of the input b at *)
(* a, read at RAX - 12, ..., RAX, RAX being a + 12 + 13 i, become 8         *)
(* coefficients 2^12 - t, stored (most of them more than once) at [rsp + rcx *)
(* + ob - 28 + 4 k], RCX being 28 + 32 i: 32 iterations, with R12, R14 and   *)
(* R15 among the temporaries.                                                *)
(* ------------------------------------------------------------------------- *)

let T0U_ALIASES =
  map (fun k ->
    Printf.sprintf "word_add (word_add a (word (13 * i + 12))) (word %s):int64 = word_add a (word (%s))"
      (disp_num (k - 12)) (if k = 0 then "13 * i" else Printf.sprintf "13 * i + %d" k)) (0--11);;

let T0U_STMT fn loop exit ob =
  parse_term(Printf.sprintf
  "exists f_events.
  forall e a rsp0 pc (b:num->byte).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    ALL (nonoverlapping (word_add rsp0 (word %d),1024))
        [(a,416); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word_add a (word 12) /\\
              read RCX s = word 28 /\\
              (!j. j < 416 ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word_add a (word 428) /\\
              read RCX s = word 1052 /\\
              (!j. j < 416 ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s =
                               mld_polyt0_unpack b i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events a rsp0 pc /\\
                 memaccess_inbounds e2 [a,416; word_add rsp0 (word %d),1024]
                                       [word_add rsp0 (word %d),1024]))
         (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11; R12; R14; R15] ,,
          MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(word_add rsp0 (word %d),1024)])"
  ob image_mc fn loop fn exit ob ob ob ob);;

let T0U_TAC exec fn loop exit ob =
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (rsp0:int64) (pc:num).
      APPEND (f_ev_epil a rsp0 pc)
       (APPEND (ENUMERATEL 32 (\i. f_ev_loop a rsp0 pc i)) (f_ev_prol a rsp0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `rsp0:int64`; `pc:num`; `b:num->byte`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read RSP s = rsp0 /\\
          read RAX s = word_add a (word (13 * i + 12)) /\\
          read RCX s = word (28 + 32 * i) /\\
          (!j. j < 416
               ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\\
          (!j. j < 8 * i
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s =
                   mld_polyt0_unpack b j)" ob)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0; ADD_CLAUSES] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    CHUNK_INPUT_TAC `b:num->byte` 13 THEN
    INPUT_ALT_ADDR_TAC `a:int64` THEN
    ALIAS_ASSUME_TAC T0U_ALIASES THEN
    VAL_INT64_TAC `28 + 32 * i` THEN
    X86_STEPS_TAC exec (1--102) THEN
    CHUNK_FULL_FINAL3_TAC ob
      [ARITH_RULE `13 * (i + 1) + 12 = 13 * i + 25`; ARITH_RULE `28 + 32 * (i + 1) = 28 + 32 * i + 32`]
      ALL_TAC mld_polyt0_unpack `b:num->byte`;
    FULL_EXIT0_TAC];;

let PROVE_T0U fn loop exit ob =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(T0U_STMT fn loop exit ob, T0U_TAC exec fn loop exit ob);;

(* ------------------------------------------------------------------------- *)
(* Loops of the rows of w0 - c s2 + c t0, which address the row of w through *)
(* RBX = b (the row index being symbolic in the proof of the loop over the   *)
(* rows): the polynomial at b, addressed as [rbx + rax * 4 + d], d being     *)
(* negative for the first chunks. The facts about b + j are kept in the form *)
(* word_add b (word (0 + ...)) of LINEAR_ADDR_CONV_B with the base 0, and    *)
(* the simulator's addresses are aliased to that form before the steps.      *)
(* ------------------------------------------------------------------------- *)

(* The normalization of LINEAR_ADDR_CONV_B applied only to the offsets n of
   the addresses word_add p (word n), so that a canonical offset 0 + (s * i +
   d) is not normalized again inside (ADDR_LINEAR_BASES_TAC descends into the
   subterms of an offset that is already in its canonical form). *)
let LIN_WORD_CONV bases tm =
  match tm with
    Comb(Comb(Const("word_add",_),p),Comb(Const("word",_),n))
      when type_of n = `:num` && not(is_numeral n) && is_comb n ->
        RAND_CONV(RAND_CONV(LINEAR_ADDR_CONV_B bases)) tm
  | _ -> failwith "LIN_WORD_CONV";;

let ADDR_LIN_WORD_TAC bases =
  let pat = `read (memory :> c) (s:x86state) = v` in
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] pat) (concl th)
    then (try CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV(LIN_WORD_CONV bases))) th
          with Failure _ -> th)
    else th);;

let GOAL_LIN_WORD_TAC bases =
  CONV_TAC(ONCE_DEPTH_CONV(LIN_WORD_CONV bases));;

let MERGE_LIN_W_TAC n bases tm =
  MP_TAC(CONV_RULE(RAND_CONV(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                             ONCE_DEPTH_CONV(LIN_WORD_CONV bases)))
          (READ_MEMORY_MERGE_CONV n tm)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC;;

(* CHUNKN_FULL_FINAL_TAC of inline_sign.ml with this normalization *)
let CHUNKN_FULL_FINAL_W_TAC bases n ars (extra:tactic) (spec_tac:tactic) =
  ADDR_LIN_WORD_TAC bases THEN ADDR_NORMALIZE_TAC THEN ADDR_LIN_WORD_TAC bases THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  LOOP_TEST_TAC THEN PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(REWRITE_TAC ars THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(extra THEN NO_TAC) THEN
  TRY(REWRITE_TAC[CHUNK_OUTPUT_SPLIT_N n] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[ADD_CLAUSES] THEN
      CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      GOAL_LIN_WORD_TAC bases THEN
      ASM_REWRITE_TAC[] THEN spec_tac THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* the alias of the simulator's address 4 * (idx) + d (d possibly negative)
   from b with the canonical address 0 + (s * i + c) of offset off + s i *)
let B_ALIAS_TAC (bv:string) idx d s c =
  let canon = if c = 0 then Printf.sprintf "0 + %d * i" s
              else Printf.sprintf "0 + (%d * i + %d)" s c in
  let sim = if d = 0 then Printf.sprintf "4 * (%s)" idx
            else Printf.sprintf "4 * (%s) + %s" idx (disp_num d) in
  ALIAS_ASSUME_TAC
   [Printf.sprintf "word_add %s (word (%s)):int64 = word_add %s (word (%s))"
      bv sim bv canon];;

let B_ALIGN_TAC (bv:string) s c =
  let canon = if c = 0 then Printf.sprintf "0 + %d * i" s
              else Printf.sprintf "0 + (%d * i + %d)" s c in
  SUBGOAL_THEN (parse_term(Printf.sprintf "aligned 16 (word_add %s (word (%s)):int64)" bv canon))
    ASSUME_TAC THENL
   [SUBGOAL_THEN (parse_term(Printf.sprintf
      "word_add %s (word (%s)):int64 = word_add %s (word (%d * (%d * i) + %d))"
      bv canon bv 16 (s / 16) c)) SUBST1_TAC THENL
     [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC ALIGNED_WORD_ADD THEN ASM_REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUMBER_RULE;
    ALL_TAC];;

(* mld_poly_reduce of the polynomial at b = RBX, RAX = 4 + 8 i, addressed as
   [rbx + rax * 4 - 16] and [rbx + rax * 4], with 2^22 in XMM5 and -q in XMM6 *)

let REDLOOPB_STMT fn loop exit =
  parse_term(Printf.sprintf
  "exists f_events.
  forall e b pc (x:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    aligned 16 b /\\ nonoverlapping (b,1024) (word pc,libmldsa_size)
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RBX s = b /\\ read RAX s = word 4 /\\
              read XMM5 s = word 0x00400000004000000040000000400000 /\\
              read XMM6 s = word 0xff801fffff801fffff801fffff801fff /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add b (word (4*i)))) s = x i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read RBX s = b /\\ read RAX s = word 260 /\\
              read XMM5 s = word 0x00400000004000000040000000400000 /\\
              read XMM6 s = word 0xff801fffff801fffff801fffff801fff /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add b (word (4*i)))) s = mld_poly_reduce x i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events b pc /\\
                 memaccess_inbounds e2 [b,1024] [b,1024]))
         (MAYCHANGE [RIP; RAX] ,, MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(b,1024)])"
  image_mc fn loop fn exit);;

let REDLOOPB_TAC exec fn loop exit =
  CONCRETIZE_F_EVENTS_TAC
   `\(b:int64) (pc:num).
      APPEND (f_ev_epil b pc)
       (APPEND (ENUMERATEL 32 (\i. f_ev_loop b pc i)) (f_ev_prol b pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `b:int64`; `pc:num`; `x:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec; mld_poly_reduce] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   `\i s. read RBX s = b /\
          read RAX s = word (4 + 8 * i) /\
          read XMM5 s = word 0x00400000004000000040000000400000 /\
          read XMM6 s = word 0xff801fffff801fffff801fffff801fff /\
          (!j. 8 * i <= j /\ j < 256
               ==> read(memory :> bytes32(word_add b (word(4 * j)))) s = x j) /\
          (!j. j < 8 * i
               ==> read(memory :> bytes32(word_add b (word(4 * j)))) s = mld_reduce32 (x j))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MAP_EVERY (fun n -> GHOST_INTRO_TAC (mk_var(Printf.sprintf "ymm%d_init" n,`:int256`))
                         (parse_term(Printf.sprintf "read YMM%d" n))) [0;1;2;3;4] THEN
    FULL_INIT_TAC THEN
    XMM_EXISTSTOP_TAC "top5" `YMM5` THEN XMM_EXISTSTOP_TAC "top6" `YMM6` THEN
    VAL_INT64_TAC `4 + 8 * i` THEN
    B_ALIAS_TAC "b" "4 + 8 * i" (-16) 32 0 THEN B_ALIAS_TAC "b" "4 + 8 * i" 0 32 16 THEN
    B_ALIGN_TAC "b" 32 0 THEN B_ALIGN_TAC "b" 32 16 THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MATCH_MP (CHUNK_INPUT_SPLIT_N 8) (ASSUME `i < 32`)] o
      check (fun th -> free_in `x:num->int32` (concl th) && not(free_in `mld_reduce32` (concl th)) && is_forall(concl th))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    STRIP_TAC THEN ADDR_LIN_WORD_TAC [0] THEN
    MERGE_LIN_W_TAC 2 [0] `read(memory :> bytes128(word_add b (word (0 + 32 * i)))) s0` THEN
    MERGE_LIN_W_TAC 2 [0] `read(memory :> bytes128(word_add b (word (0 + (32 * i + 16))))) s0` THEN
    VERIF_SSE_STEPS_TAC exec (1--24) THEN X86_STEPS_TAC exec (25--27) THEN
    MAP_EVERY (fun t ->
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(SIMD_SIMPLIFY_CONV []) o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
        check (fun th -> can (term_match [] `read (memory :> bytes128 a) s = x`) (concl th) &&
                         lhand(concl th) = t)))
      [`read(memory :> bytes128(word_add b (word (0 + 32 * i)))) s27`;
       `read(memory :> bytes128(word_add b (word (0 + (32 * i + 16))))) s27`] THEN
    CHUNKN_FULL_FINAL_W_TAC [0] 8
      [ARITH_RULE `8 * (i + 1) = 8 * i + 8`; ARITH_RULE `4 + 8 * (i + 1) = 4 + 8 * i + 8`]
      (REWRITE_TAC[XMM5; XMM6; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST)
      (REWRITE_TAC[REDUCE32_LANE_SSE]);
    FULL_EXIT0_TAC];;

let PROVE_REDLOOPB fn loop exit =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(REDLOOPB_STMT fn loop exit, REDLOOPB_TAC exec fn loop exit);;

(* mld_poly_sub x y of x at b = RBX (updated) and y at rsp0 + yb, RAX = 12 +
   16 i, x addressed as [rbx + rax * 4 - 48 + 16 g] and y as [rsp + rax * 4 +
   yb - 48 + 16 g]: the loop of w0 - c s2 *)

let SUBLOOPB_STMT fn loop exit yb =
  parse_term(Printf.sprintf
  "exists f_events.
  forall e b rsp0 pc (x:num->int32) (y:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    aligned 16 b /\\ aligned 16 (word_add rsp0 (word %d)) /\\
    ALL (nonoverlapping (b,1024))
        [(word_add rsp0 (word %d),1024); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RBX s = b /\\ read RSP s = rsp0 /\\ read RAX s = word 12 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add b (word (4*i)))) s = x i) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = y i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read RBX s = b /\\ read RSP s = rsp0 /\\ read RAX s = word 268 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add b (word (4*i)))) s = mld_poly_sub x y i) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = y i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events b rsp0 pc /\\
                 memaccess_inbounds e2 [b,1024; word_add rsp0 (word %d),1024] [b,1024]))
         (MAYCHANGE [RIP; RAX] ,, MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(b,1024)])"
  yb yb image_mc fn loop yb fn exit yb yb);;

let SUBLOOPB_TAC exec fn loop exit yb =
  let ky = yb - 48 in
  CONCRETIZE_F_EVENTS_TAC
   `\(b:int64) (rsp0:int64) (pc:num).
      APPEND (f_ev_epil b rsp0 pc)
       (APPEND (ENUMERATEL 16 (\i. f_ev_loop b rsp0 pc i)) (f_ev_prol b rsp0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `b:int64`; `rsp0:int64`; `pc:num`;
                       `x:num->int32`; `y:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec; mld_poly_sub] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `16` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read RBX s = b /\\ read RSP s = rsp0 /\\
          read RAX s = word (12 + 16 * i) /\\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = y j) /\\
          (!j. 16 * i <= j /\\ j < 256
               ==> read(memory :> bytes32(word_add b (word(4 * j)))) s = x j) /\\
          (!j. j < 16 * i
               ==> read(memory :> bytes32(word_add b (word(4 * j)))) s =
                   word_sub (x j) (y j))" yb)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MAP_EVERY (fun n -> GHOST_INTRO_TAC (mk_var(Printf.sprintf "ymm%d_init" n,`:int256`))
                         (parse_term(Printf.sprintf "read YMM%d" n))) [0;1;2;3] THEN
    FULL_INIT_TAC THEN
    VAL_INT64_TAC `12 + 16 * i` THEN
    MAP_EVERY (fun g -> B_ALIAS_TAC "b" "12 + 16 * i" (16 * g - 48) 64 (16 * g) THEN
                        B_ALIGN_TAC "b" 64 (16 * g)) [0;1;2;3] THEN
    MAP_EVERY (fun k -> ALIGN16_IDX_TAC `rsp0:int64`
        (parse_term(Printf.sprintf "4 * (12 + 16 * i) + %d" k)))
      [ky; ky + 16; ky + 32; ky + 48] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MATCH_MP (CHUNK_INPUT_SPLIT_N 16) (ASSUME `i < 16`)] o
      check (fun th -> free_in `x:num->int32` (concl th) && not(free_in `word_sub:int32->int32->int32` (concl th)) && is_forall(concl th))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    STRIP_TAC THEN ADDR_LIN_WORD_TAC [0; yb] THEN
    SUBGOAL_THEN (parse_term(Printf.sprintf "!k. k < 16 ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * (16 * i + k))))) s0 = (y:num->int32)(16 * i + k)" yb)) MP_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    STRIP_TAC THEN ADDR_LIN_WORD_TAC [0; yb] THEN
    MAP_EVERY (fun g ->
      let canon = if g = 0 then "0 + 64 * i" else Printf.sprintf "0 + (64 * i + %d)" (16 * g) in
      MERGE_LIN_W_TAC 2 [0; yb]
        (parse_term(Printf.sprintf "read(memory :> bytes128(word_add b (word (%s)))) s0" canon)) THEN
      MERGE_LIN_W_TAC 2 [0; yb]
        (parse_term(Printf.sprintf "read(memory :> bytes128(word_add rsp0 (word (4 * (12 + 16 * i) + %d)))) s0" (ky + 16 * g))))
      [0;1;2;3] THEN
    VERIF_SSE_STEPS_TAC exec (1--12) THEN X86_STEPS_TAC exec (13--15) THEN
    MAP_EVERY (fun g ->
      let canon = if g = 0 then "0 + 64 * i" else Printf.sprintf "0 + (64 * i + %d)" (16 * g) in
      let t = parse_term(Printf.sprintf "read(memory :> bytes128(word_add b (word (%s)))) s15" canon) in
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(SIMD_SIMPLIFY_CONV []) o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
        check (fun th -> lhand(concl th) = t))) [0;1;2;3] THEN
    CHUNKN_FULL_FINAL_W_TAC [0; yb] 16
      [ARITH_RULE `16 * (i + 1) = 16 * i + 16`; ARITH_RULE `12 + 16 * (i + 1) = 12 + 16 * i + 16`] ALL_TAC ALL_TAC;
    FULL_EXIT0_TAC];;

let PROVE_SUBLOOPB fn loop exit yb =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(SUBLOOPB_STMT fn loop exit yb, SUBLOOPB_TAC exec fn loop exit yb);;

(* mld_poly_add y x of x at rsp0 + xb and y at b = RBX (updated), RAX = 12 +
   16 i, x addressed as [rsp + rax * 4 + xb - 48 + 16 g] and y as [rbx + rax
   * 4 - 48 + 16 g]: the loop of w0 - c s2 + c t0 *)

let ADDLOOPB_STMT fn loop exit xb =
  parse_term(Printf.sprintf
  "exists f_events.
  forall e b rsp0 pc (x:num->int32) (y:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    aligned 16 b /\\ aligned 16 (word_add rsp0 (word %d)) /\\
    ALL (nonoverlapping (b,1024))
        [(word_add rsp0 (word %d),1024); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RBX s = b /\\ read RSP s = rsp0 /\\ read RAX s = word 12 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = x i) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add b (word (4*i)))) s = y i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read RBX s = b /\\ read RSP s = rsp0 /\\ read RAX s = word 268 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = x i) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add b (word (4*i)))) s = mld_poly_add y x i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events b rsp0 pc /\\
                 memaccess_inbounds e2 [word_add rsp0 (word %d),1024; b,1024] [b,1024]))
         (MAYCHANGE [RIP; RAX] ,, MAYCHANGE [ZMM0; ZMM1] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(b,1024)])"
  xb xb image_mc fn loop xb fn exit xb xb);;

let ADDLOOPB_TAC exec fn loop exit xb =
  let kx = xb - 48 in
  CONCRETIZE_F_EVENTS_TAC
   `\(b:int64) (rsp0:int64) (pc:num).
      APPEND (f_ev_epil b rsp0 pc)
       (APPEND (ENUMERATEL 16 (\i. f_ev_loop b rsp0 pc i)) (f_ev_prol b rsp0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `b:int64`; `rsp0:int64`; `pc:num`;
                       `x:num->int32`; `y:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec; mld_poly_add] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `16` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read RBX s = b /\\ read RSP s = rsp0 /\\
          read RAX s = word (12 + 16 * i) /\\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = x j) /\\
          (!j. 16 * i <= j /\\ j < 256
               ==> read(memory :> bytes32(word_add b (word(4 * j)))) s = y j) /\\
          (!j. j < 16 * i
               ==> read(memory :> bytes32(word_add b (word(4 * j)))) s =
                   word_add (y j) (x j))" xb)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MAP_EVERY (fun n -> GHOST_INTRO_TAC (mk_var(Printf.sprintf "ymm%d_init" n,`:int256`))
                         (parse_term(Printf.sprintf "read YMM%d" n))) [0;1] THEN
    FULL_INIT_TAC THEN
    VAL_INT64_TAC `12 + 16 * i` THEN
    MAP_EVERY (fun g -> B_ALIAS_TAC "b" "12 + 16 * i" (16 * g - 48) 64 (16 * g) THEN
                        B_ALIGN_TAC "b" 64 (16 * g)) [0;1;2;3] THEN
    MAP_EVERY (fun k -> ALIGN16_IDX_TAC `rsp0:int64`
        (parse_term(Printf.sprintf "4 * (12 + 16 * i) + %d" k)))
      [kx; kx + 16; kx + 32; kx + 48] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MATCH_MP (CHUNK_INPUT_SPLIT_N 16) (ASSUME `i < 16`)] o
      check (fun th -> free_in `y:num->int32` (concl th) && not(free_in `word_add:int32->int32->int32` (concl th)) && is_forall(concl th))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    STRIP_TAC THEN ADDR_LIN_WORD_TAC [0; xb] THEN
    SUBGOAL_THEN (parse_term(Printf.sprintf "!k. k < 16 ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * (16 * i + k))))) s0 = (x:num->int32)(16 * i + k)" xb)) MP_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    STRIP_TAC THEN ADDR_LIN_WORD_TAC [0; xb] THEN
    MAP_EVERY (fun g ->
      let canon = if g = 0 then "0 + 64 * i" else Printf.sprintf "0 + (64 * i + %d)" (16 * g) in
      MERGE_LIN_W_TAC 2 [0; xb]
        (parse_term(Printf.sprintf "read(memory :> bytes128(word_add b (word (%s)))) s0" canon)) THEN
      MERGE_LIN_W_TAC 2 [0; xb]
        (parse_term(Printf.sprintf "read(memory :> bytes128(word_add rsp0 (word (4 * (12 + 16 * i) + %d)))) s0" (kx + 16 * g))))
      [0;1;2;3] THEN
    VERIF_SSE_STEPS_TAC exec (1--12) THEN X86_STEPS_TAC exec (13--15) THEN
    MAP_EVERY (fun g ->
      let canon = if g = 0 then "0 + 64 * i" else Printf.sprintf "0 + (64 * i + %d)" (16 * g) in
      let t = parse_term(Printf.sprintf "read(memory :> bytes128(word_add b (word (%s)))) s15" canon) in
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(SIMD_SIMPLIFY_CONV []) o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
        check (fun th -> lhand(concl th) = t))) [0;1;2;3] THEN
    CHUNKN_FULL_FINAL_W_TAC [0; xb] 16
      [ARITH_RULE `16 * (i + 1) = 16 * i + 16`; ARITH_RULE `12 + 16 * (i + 1) = 12 + 16 * i + 16`]
      ALL_TAC (REWRITE_TAC[WORD_ADD_SYM]);
    FULL_EXIT0_TAC];;

let PROVE_ADDLOOPB fn loop exit xb =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(ADDLOOPB_STMT fn loop exit xb, ADDLOOPB_TAC exec fn loop exit xb);;

(* ------------------------------------------------------------------------- *)
(* mld_polyz_pack_17 of z at c (RAX = c + 12 + 16 i, loads at RAX - 12, ..., *)
(* RAX) into the 576 bytes at op (R10 = op + 7, RCX = 9 i, stores at [r10 +  *)
(* rcx - 7], ..., [r10 + rcx], the first and the last of 16 bits): 64        *)
(* iterations. The stores have the aliases of op + 9 i + k.                  *)
(* ------------------------------------------------------------------------- *)

let ZPACK17_ALIASES =
  map (fun k ->
    let r = if k = 0 then "9 * i" else Printf.sprintf "9 * i + %d" k in
    if k = 7 then
      Printf.sprintf "word_add (word_add op (word 7)) (word (1 * (9 * i))):int64 = word_add op (word (%s))" r
    else
      Printf.sprintf "word_add (word_add op (word 7)) (word (1 * (9 * i) + %s)):int64 = word_add op (word (%s))"
        (disp_num (k - 7)) r) [0;2;3;4;5;6;7];;

(* the two 16-bit stores of an iteration as their bytes *)
let ZPACK_SPLIT16_TAC sn =
  let pat = parse_term(Printf.sprintf "read (memory :> bytes16 (word_add op a)) %s = v" sn) in
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (term_match [] pat) (concl th)
    then STRIP_ASSUME_TAC(CONV_RULE(SIMD_SIMPLIFY_CONV []) (CONV_RULE(READ_MEMORY_SPLIT_CONV 1) th))
    else NO_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC]) THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV));;

(* the LEA of 4 times a register, and the loop test RCX + 9 = 576, as the
   simulation leaves them *)
let ZP_LEA4 = prove
 (`!y:int64. word (0 + 4 * val y):int64 = word_shl y 2`,
  GEN_TAC THEN REWRITE_TAC[ADD_CLAUSES; WORD_SHL_AS_MUL] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_MUL; WORD_VAL]);;

let ZPACK17_TEST = prove
 (`!i. i < 64
       ==> (val(word(9 * i + 18446744073709551049):int64) = 0 <=> ~(i + 1 < 64))`,
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC NUM_REDUCE_CONV);;

let ZPACK17_STMT fn loop exit =
  parse_term(Printf.sprintf
  "exists f_events.
  forall e c op pc (z:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    ALL (nonoverlapping (op,576)) [(c,1024); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RAX s = word_add c (word 12) /\\ read RCX s = word 0 /\\
              read R10 s = word_add op (word 7) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add c (word (4*i)))) s = z i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read RAX s = word_add c (word 1036) /\\ read RCX s = word 576 /\\
              read R10 s = word_add op (word 7) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add c (word (4*i)))) s = z i) /\\
              (!j. j < 576 ==> read (memory :> bytes8 (word_add op (word j))) s =
                               mld_polyz_pack_17 z j) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events c op pc /\\
                 memaccess_inbounds e2 [c,1024; op,576] [op,576]))
         (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; RDI; R8; R9] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(op,576)])"
  image_mc fn loop fn exit);;

let ZPACK17_TAC exec fn loop exit =
  CONCRETIZE_F_EVENTS_TAC
   `\(c:int64) (op:int64) (pc:num).
      APPEND (f_ev_epil c op pc)
       (APPEND (ENUMERATEL 64 (\i. f_ev_loop c op pc i)) (f_ev_prol c op pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `c:int64`; `op:int64`; `pc:num`; `z:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `64` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   `\i s. read RAX s = word_add c (word (16 * i + 12)) /\
          read RCX s = word (9 * i) /\
          read R10 s = word_add op (word 7) /\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add c (word(4 * j)))) s = z j) /\
          (!j. j < 9 * i
               ==> read(memory :> bytes8(word_add op (word j))) s = mld_polyz_pack_17 z j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    CHUNK_INPUT_TAC `z:num->int32` 4 THEN
    INPUT_ALT_ADDR_TAC `c:int64` THEN
    VAL_INT64_TAC `9 * i` THEN
    ALIAS_ASSUME_TAC (W1PACKS_ALIASES @ ZPACK17_ALIASES) THEN
    X86_STEPS_TAC exec (1--35) THEN
    ZPACK_SPLIT16_TAC "s35" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `i:num` ZPACK17_TEST) (ASSUME `i < 64`);
                                G1A_ZX_MOD16; ZP_LEA4]) THEN
    CHUNK_FULL_FINAL_ARS_TAC [ARITH_RULE `9 * (i + 1) = 9 * i + 9`; ARITH_RULE `16 * (i + 1) = 16 * i + 16`]
      mld_polyz_pack_17 `z:num->int32`;
    FULL_EXIT0_TAC];;

let PROVE_ZPACK17 fn loop exit =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(ZPACK17_STMT fn loop exit, ZPACK17_TAC exec fn loop exit);;

(* ------------------------------------------------------------------------- *)
(* mld_polyw1_unpack_88 of the 192 bytes b at rsp0 + ib (3 bytes, read as   *)
(* [rsp + idx + ib - r0 + k] with the index register idx = r0 + 3 i, become  *)
(* 4 coefficients of 6 bits, stored at RCX - 12, ..., RCX, RCX = c + 12 + 16 *)
(* i): 64 iterations, the unpacking of w1 in mld_pack_sig_h. The            *)
(* temporaries are the registers of regs.                                    *)
(* ------------------------------------------------------------------------- *)

let W1UNPACK_STMT fn loop exit idx r0 ib regs =
  parse_term(Printf.sprintf
  "exists f_events.
  forall e c rsp0 pc (b:num->byte).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    ALL (nonoverlapping (c,1024))
        [(word_add rsp0 (word %d),192); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read %s s = word %d /\\
              read RCX s = word_add c (word 12) /\\
              (!j. j < 192 ==> read(memory :> bytes8(word_add rsp0 (word (%d + j)))) s = b j) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read %s s = word %d /\\
              read RCX s = word_add c (word 1036) /\\
              (!j. j < 192 ==> read(memory :> bytes8(word_add rsp0 (word (%d + j)))) s = b j) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add c (word (4*i)))) s =
                               mld_polyw1_unpack_88 b i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events c rsp0 pc /\\
                 memaccess_inbounds e2 [word_add rsp0 (word %d),192; c,1024] [c,1024]))
         (MAYCHANGE [RIP; %s; RCX; %s] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(c,1024)])"
  ib image_mc fn loop idx r0 ib fn exit idx (r0 + 192) ib ib idx regs);;

let W1UNPACK_TAC exec fn loop exit idx r0 ib =
  let ix = idx_expr r0 3 in
  CONCRETIZE_F_EVENTS_TAC
   `\(c:int64) (rsp0:int64) (pc:num).
      APPEND (f_ev_epil c rsp0 pc)
       (APPEND (ENUMERATEL 64 (\i. f_ev_loop c rsp0 pc i)) (f_ev_prol c rsp0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `c:int64`; `rsp0:int64`; `pc:num`; `b:num->byte`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `64` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read RSP s = rsp0 /\\
          read %s s = word (%s) /\\
          read RCX s = word_add c (word (16 * i + 12)) /\\
          (!j. j < 192
               ==> read(memory :> bytes8(word_add rsp0 (word (%d + j)))) s = b j) /\\
          (!j. j < 4 * i
               ==> read(memory :> bytes32(word_add c (word(4 * j)))) s =
                   mld_polyw1_unpack_88 b j)" idx ix ib)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0; ADD_CLAUSES] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    IDX_BYTE_FACTS_TAC `b:num->byte` 3 ib r0 3 THEN
    VAL_INT64_TAC (parse_term ix) THEN
    ALIAS_ASSUME_TAC W1PACKS_ALIASES THEN
    X86_STEPS_TAC exec (1--23) THEN
    CHUNK_FULL_FINAL_ARS_TAC
      [ARITH_RULE (parse_term(if r0 = 0 then "3 * (i + 1) = 3 * i + 3"
                              else Printf.sprintf "%d + 3 * (i + 1) = %d + 3 * i + 3" r0 r0));
       ARITH_RULE `16 * (i + 1) = 16 * i + 16`]
      mld_polyw1_unpack_88 `b:num->byte`;
    FULL_EXIT0_TAC];;

let PROVE_W1UNPACK fn loop exit idx r0 ib regs =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(W1UNPACK_STMT fn loop exit idx r0 ib regs, W1UNPACK_TAC exec fn loop exit idx r0 ib);;
