(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas for the control-heavy scalar loops of the hint handling that clang *)
(* 23 has inlined into mldsa{44,65,87}_verify_internal (mld_sig_unpack_hints *)
(* of packing.c) and mldsa{44,65,87}_signature_internal (mld_pack_sig_h).    *)
(* They are stated and used as the loop lemmas of inline_sign.ml: from the   *)
(* head of a loop to its exits, with the registers as parameters.            *)
(*                                                                           *)
(* STATUS (agent arm-C3):                                                    *)
(*   * INLINE_ZCHK_LOOP (shape 47): proved, instances below.                 *)
(*   * The loop of shapes 53/54 (INLINE_HUNP_LOOP): proved for              *)
(*     mldsa44_verify_internal (114 seconds), see the end of the file.       *)
(*   * Shapes 52 and 91 are not loops (see below). pack_sig_h: analysis     *)
(*     only (see the end of this comment); nothing is proved.                *)
(*                                                                           *)
(* The CFG of mld_sig_unpack_hints for polynomial i in verify_internal, with *)
(* the addresses of mldsa44_verify_internal (K = 4, omega = 80; the others   *)
(* have the same code, with other registers: see the instance lists). P is   *)
(* the address of the hints, x26 (65, 87: x27); x27 (65, 87: x28) is the     *)
(* polynomial h; x21 (65, 87: x24) = new = P[80 + i], x25 = old = P[79 + i]  *)
(* or 0 for i = 0, as zero-extended bytes:                                   *)
(*                                                                           *)
(*   +0x233c  i := [sp + 440]; cbz i, +0x2368                                *)
(*   +0x2344..+0x2364  (i != 0) load old, new; cmp new, 80; b.ls join5 else  *)
(*                     b join3 (failure, w26 = -6 is set at +0x2354)         *)
(*   +0x2368..+0x2380  (i = 0)  old := 0, load new; same test                *)
(*   join5 +0x2384    cmp old, new; b.hi join3 (failure)                     *)
(*   +0x238c  x19 := i; memset(x27, 0, 1024)  (a call, not a loop)           *)
(*   +0x23a0  cmp old, new; mov x3 := i, x26 := P, w13 := 1; b.cs join6      *)
(*   +0x23b4  the first iteration of the loop of mld_unpack_hints, peeled:   *)
(*            h[P[old]] := 1; x9 := old + 1; b.ne +0x24a0 if old + 1 != new  *)
(*            else falls to join6                                            *)
(*   +0x24a0  x10 := [sp + 24] (= P + 1) + old (x8 = old); b loop13          *)
(*   join6 +0x23cc  constants of poly_use_hint; cmp x3, 3; b.ne join7; cmp   *)
(*            new, 80; b.cs join7; then LOOP11 (shape 47, INLINE_ZCHK_LOOP): *)
(*            the unused index bytes P[new..79] must be zero; failure exit   *)
(*            is the jump cbnz w8, join2 (= +0x96c, w26 := -6), ok exit      *)
(*            join7 (+0x240c)                                                *)
(*   loop13 +0x24c0 (INLINE_HUNP_LOOP, shapes 54 and 53)                      *)
(*            ldrb w11, [x10]; cmp x9, x8; b.ls join9 (dead: x9 > x8);       *)
(*            ldurb w12, [x10, -1]; cmp w11, w12; b.hi join9;                *)
(*            +0x24d8 (fall through: P[j] <= P[j - 1], failure; code there   *)
(*            is `b join2`)                                                  *)
(*   join9 +0x24ac  x9 += 1; x10 += 1; h[P[j]] := 1; cmp x21, x9; b.eq      *)
(*            join6 (done: j + 1 = new), else falls to loop13 (+0x24c0).     *)
(*                                                                           *)
(* How the parent connects the pieces for polynomial i (all straight-line,   *)
(* except the memset call):                                                  *)
(*   +0x233c .. +0x2388  the tests of old, new (three branches to join3)     *)
(*   +0x238c .. +0x239c  memset call (H_MEMSET contract: h := 0)             *)
(*   +0x23a0 .. +0x23b0  branch old >= new -> join6 (hints of the            *)
(*                       polynomial: none)                                   *)
(*   +0x23b4 .. +0x23c8  peeled iteration j = old: h[P[old]] := 1; if        *)
(*                       old + 1 = new -> join6, else +0x24a0 .. +0x24a8     *)
(*                       and then INLINE_HUNP_LOOP at +0x24c0 with           *)
(*                         x9 = old + 1, x8 = old, x10 = P + (old + 1),      *)
(*                         x13 = 1, x27 = h, x21 = new, s = old, w = new;    *)
(*                       h before the loop is the memset result with         *)
(*                       h[P[old]] := 1, i.e. inline_hset (\q. 0) P old      *)
(*                       (old + 1); after the loop (exit at join6) it is     *)
(*                       inline_hset (\q. 0) P old new = mld_unpack_hints,   *)
(*                       by inline_hset's definition (the lemma is           *)
(*                       INLINE_HSET_0 for the first and INLINE_HSET of this  *)
(*                       file for the second; the glue is not proved).       *)
(*   join6 +0x23cc .. +0x23f4  tests i = 3, new < 80, then INLINE_ZCHK_LOOP  *)
(*   The result is -1 exactly if one of the exits to join2/join3 is taken,   *)
(*   which is mld_unpack_hints_ret (the exits are the negations of the       *)
(*   conjuncts of mld_unpack_hints_ok).                                      *)
(*                                                                           *)
(* Shapes 52 (+0x23cc..+0x24c0) and 91 (65: +0x24bc..+0x2598) are not loops: *)
(* the loop detection of the layout lists join6 as the head of a loop      *)
(* because loop13 branches back to it with b.eq +0x24bc; join6 is the exit   *)
(* of the hints loop and the whole range in between is straight-line code    *)
(* of the use_hint loop (shapes 13/14/15), laid out by the compiler between  *)
(* the two. Nothing to prove for them as loops.                              *)
(*                                                                           *)
(* pack_sig_h (signature_internal, 44: +0x4ef8..+0x5448; analysis only).     *)
(* For each polynomial the clang code fuses mld_make_hint with the packing   *)
(* into one loop over j = 0..255 with three paths (a0 = w0[j], a1 = w1[j],   *)
(* w1 unpacked into the scratch polynomial by the polyw1_unpack loop before) *)
(* and k = x8 (w8) the number of hints so far:                               *)
(*   loop46 (+0x4f28) head, +0x4f14/+0x4f18 the store block (strb j, [x27,k];  *)
(*   k++), join8 +0x4f1c (j++; b.eq exit2 when j = 256), exits: loop46_exit2   *)
(*   (+0x501c, all 256 done) and +0x4f54 (k = 80 and another hint: return 1).*)
(*   The three paths of an iteration: no hint (b.cc join8 at +0x4f48), hint  *)
(*   with k < 80 (+0x4f4c cmp k, 80; b.ne +0x4f14 store), hint with k = 80   *)
(*   (fall to +0x4f54). The loop is entered by `b loop46` into its head at    *)
(*   +0x4f28 after j := 0, so the exec range of a lemma must be from         *)
(*   +0x4f14 (the store block) to +0x4f54, with head = loop46 (+0x4f28).     *)
(*   loop48/50/52 (+0x5174, +0x52d8, +0x545c) are the same loop for          *)
(*   polynomials 1, 2, 3 with another block order (the test k = 80 comes     *)
(*   first, at join12/join15/join16), register choices (x16, x17, x18 as    *)
(*   pointer to w0) and the make_hint compare done with cset + tbnz instead  *)
(*   of the ccmp chain (loop46 is the polynomial 0 version): four shapes    *)
(*   (46: shapes 27/28/32/33/..., 48/52: 32/33/36, 50: 36...). The lemma is  *)
(*   the same for all: with hb j = mld_make_hint_88 (w0 j) (w1 j) (32 for    *)
(*   65 and 87), k0 the incoming k:                                          *)
(*     ok exit  iff  k0 + mld_hint_count hb 256 <= 80, with                  *)
(*       byte t of the hints := mld_hint_index hb 256 (t - k0) for           *)
(*       k0 <= t < k0 + count, others unchanged, w8 = k0 + count             *)
(*     fail exit otherwise (the bytes are unspecified).                      *)
(*   They fit the convention (one head, two exits, three paths of the        *)
(*   iteration) but are NOT written: the proofs follow the pattern of        *)
(*   INLINE_HUNP_LOOP below, with GLUE_PSH_* of utils/mldsa_native_hints.ml  *)
(*   for the three paths.                                                    *)
(* The larger "loops" of the pack_sig_h list (236..1608 instructions) are    *)
(* address ranges around the jumps back to join9/join11 and the loops        *)
(* above; they are not loops.                                                *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_hints.ml";;
needs "common/mldsa_native_hints.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign.ml";;


(* ------------------------------------------------------------------------- *)
(* Shape 47: the loop that checks that the unused index bytes P[n..79] of    *)
(* the hints are zero (last polynomial). Registers:                          *)
(*   R0 = x8 (temporary), R1 = x26 = P, R2 = x21 = index n (< 80)            *)
(*     loop: ldrb w.R0, [R1, R2]; cbnz w.R0, <failure exit>;                 *)
(*           add R2, R2, #1; cmp R2, #0x50; b.ne loop                        *)
(* Exits: the end of the loop (R2 = 80) if all bytes are zero, and the       *)
(* jump of cbnz (the PC is the failure exit, join2) at the first nonzero     *)
(* byte. The PC after the lemma is word(pc + exit) in the first case and     *)
(* word(pc + fail) in the second. The events depend on the bytes b j of P    *)
(* (the hints, declassified by the C code as in the gcc proofs).             *)
(* ------------------------------------------------------------------------- *)


let INLINE_ZRUN = new_definition
 `inline_zrun (b:num->byte) n =
    minimal j. n <= j /\ (j = 80 \/ ~(b j = word 0))`;;

let INLINE_ZSTEPS = new_definition
 `inline_zsteps (b:num->byte) n =
    if inline_zrun b n = 80 then 80 - n else inline_zrun b n - n + 1`;;


let INLINE_ZCHK_LOOP_TERM mc loop exit fail (rs:string list) =
  let r k = List.nth rs k in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e sg (b:num->byte) n pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        n < 80
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read %s s = sg /\\ read %s s = word n /\\
                  (!j. j < 80
                       ==> read(memory :> bytes8(word_add sg (word j))) s =
                           b j) /\\
                  read events s = e)
             (\\s. read PC s = word (if (!j. n <= j /\\ j < 80 ==> b j = word 0)
                                    then pc + %s else pc + %s) /\\
                  ((!j. n <= j /\\ j < 80 ==> b j = word 0)
                   ==> read %s s = word 80) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events b n sg pc /\\
                     memaccess_inbounds e2 [sg,80] []))
             (MAYCHANGE [PC; %s; %s] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [events])"
   mc loop (r 1) (r 2) exit fail (r 2) (r 0) (r 2));;


let INLINE_ZRUN_FACTS = prove
 (`!(b:num->byte) n.
     n < 80
     ==> n <= inline_zrun b n /\ inline_zrun b n <= 80 /\
         (inline_zrun b n = 80 \/ ~(b(inline_zrun b n) = word 0)) /\
         (!j. n <= j /\ j < inline_zrun b n ==> b j = word 0) /\
         ((!j. n <= j /\ j < 80 ==> b j = word 0) <=> inline_zrun b n = 80)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `?j. n <= j /\ (j = 80 \/ ~((b:num->byte) j = word 0))`
   (fun th -> MP_TAC(MATCH_MP (fst(EQ_IMP_RULE(REWRITE_RULE[GSYM INLINE_ZRUN] (BETA_RULE
     (SPEC `\j. n <= j /\ (j = 80 \/ ~((b:num->byte) j = word 0))` MINIMAL))))) th)) THENL
   [EXISTS_TAC `80` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `m = inline_zrun (b:num->byte) n` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `m <= 80` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `80` o check (fun th -> is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!j. n <= j /\ j < m ==> (b:num->byte) j = word 0` ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(j = 80)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th -> is_forall(concl th) && free_in `80` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    DISCH_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check(fun th -> is_forall(concl th) && free_in `m:num` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let INLINE_MIN_LE_L = ARITH_RULE `!n m. n <= m ==> MIN n m = n`;;
let INLINE_MIN_GE_L = ARITH_RULE `!n m. m <= n ==> MIN n m = m`;;


let INLINE_ZFACTS_TAC =
  REWRITE_TAC[INLINE_ZSTEPS] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b:num->byte`;`n:num`] INLINE_ZRUN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `m = inline_zrun (b:num->byte) n` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `m = 80` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ASM_REWRITE_TAC[];;

let INLINE_ZSTEPS_POS = prove
 (`!(b:num->byte) n. n < 80 ==> 0 < inline_zsteps b n`,
  REPEAT GEN_TAC THEN INLINE_ZFACTS_TAC THEN ASM_ARITH_TAC);;

let INLINE_ZSTEPS_LT = prove
 (`!(b:num->byte) n p. n < 80 /\ p < inline_zsteps b n
        ==> n + p < 80 /\ n + p <= inline_zrun b n`,
  REPEAT GEN_TAC THEN INLINE_ZFACTS_TAC THEN ASM_ARITH_TAC);;

let INLINE_ZSTEPS_MID = prove
 (`!(b:num->byte) n p. n < 80 /\ p + 1 < inline_zsteps b n
        ==> b(n + p) = word 0 /\ n + p + 1 < 80`,
  REPEAT GEN_TAC THEN INLINE_ZFACTS_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n + p` o
    check (fun th -> is_forall(concl th))) THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let INLINE_ZSTEPS_OK = prove
 (`!(b:num->byte) n p. n < 80 /\ p + 1 = inline_zsteps b n /\
                       (!j. n <= j /\ j < 80 ==> b j = word 0)
        ==> b(n + p) = word 0 /\ n + p + 1 = 80`,
  REPEAT GEN_TAC THEN INLINE_ZFACTS_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n + p` o
    check (fun th -> is_forall(concl th))) THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let INLINE_ZSTEPS_FAIL = prove
 (`!(b:num->byte) n p. n < 80 /\ p + 1 = inline_zsteps b n /\
                       ~(!j. n <= j /\ j < 80 ==> b j = word 0)
        ==> ~(b(n + p) = word 0)`,
  REPEAT GEN_TAC THEN INLINE_ZFACTS_TAC THEN
  (SUBGOAL_THEN `n + p = m` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  ASM_MESON_TAC[]);;

let INLINE_ZRUN_OK = prove
 (`!(b:num->byte) n. n < 80 /\ (!j. n <= j /\ j < 80 ==> b j = word 0)
        ==> inline_zrun b n = 80`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b:num->byte`;`n:num`] INLINE_ZRUN_FACTS) THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[]);;

let INLINE_ZRUN_FAIL = prove
 (`!(b:num->byte) n p. n < 80 /\ p + 1 = inline_zsteps b n /\
                       ~(!j. n <= j /\ j < 80 ==> b j = word 0)
        ==> inline_zrun b n = n + p`,
  REPEAT GEN_TAC THEN INLINE_ZFACTS_TAC THEN ASM_ARITH_TAC);;

let INLINE_ZB_PC = prove(`!k. k < 80 ==> (val(word_add (word k:int64) (word 18446744073709551537)) = 0 <=> k = 79)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[VAL_EQ_0] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `word_add (word k:int64) (word 18446744073709551537) = word 0` THEN
    REWRITE_TAC[GSYM WORD_ADD; GSYM VAL_EQ; VAL_WORD; DIMINDEX_64; VAL_WORD_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_CASES_TAC `k = 79` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`k + 18446744073709551537`; `18446744073709551616`] MOD_LT) THEN
    (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN DISCH_THEN SUBST1_TAC THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN CONV_TAC WORD_REDUCE_CONV]);;

let INLINE_ZB_EQ0 = prove(`!x:byte. val(word_zx(word_zx(word_zx x:int32):int64):int32) = 0 <=> x = word 0`,
  GEN_TAC THEN REWRITE_TAC[VAL_EQ_0] THEN BITBLAST_TAC);;

let INLINE_ARITH_WITH (tms:term list) = MAP_EVERY (MP_TAC o ASSUME) tms THEN ARITH_TAC;;

let INLINE_ZTPL = `\(b:num->byte) (n:num) (sg:int64) (pc:num).
   APPEND ([]:(uarch_event)list)
    (APPEND (ENUMERATEL (inline_zsteps b n)
       (\p. if p + 1 < inline_zsteps b n then f_ev_a b n sg pc p
            else if (!j. n <= j /\ j < 80 ==> b j = word 0)
                 then f_ev_ok b n sg pc p else f_ev_fail b n sg pc p))
      ([]:(uarch_event)list))`;;

(* ------------------------------------------------------------------------- *)
(* The proof: one loop over the iterations (GLUE_ENSURES_WHILE of            *)
(* common/fips204/properties/mldsa_native_hints.ml, whose invariant has the  *)
(* PC of the head for p < N and that of the exit for p = N), with the        *)
(* events template                                                           *)
(*   ENUMERATEL N (\p. if p + 1 < N then f_ev_a .. else if ok then f_ev_ok  *)
(*                     else f_ev_fail)                                       *)
(* N = inline_zsteps b n: 80 - n if the bytes are zero, else up to and       *)
(* including the first nonzero one.                                          *)
(* ------------------------------------------------------------------------- *)

let INLINE_ZSTART_TAC exec INLINE_ZTPL inv =
  CONCRETIZE_F_EVENTS_TAC INLINE_ZTPL THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `sg:int64`; `b:num->byte`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  GLUE_EVENTS_WHILE_TAC `inline_zsteps (b:num->byte) n` inv THEN REPEAT CONJ_TAC;;

let INLINE_ZINIT_TAC =
  MP_TAC(SPECL [`b:num->byte`;`n:num`] INLINE_ZSTEPS_POS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`b:num->byte`;`n:num`] INLINE_ZRUN_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_0; ENUMERATEL; APPEND] THEN
  ASM_SIMP_TAC[INLINE_MIN_LE_L] THEN
  EXISTS_TAC `[]:(uarch_event)list` THEN REWRITE_TAC[APPEND_NIL;APPEND] THEN
  DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC;;

let INLINE_ZBODY_PREP_TAC =
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  MP_TAC(SPECL [`b:num->byte`;`n:num`;`i:num`] INLINE_ZSTEPS_LT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  (SUBGOAL_THEN `MIN (n + i) (inline_zrun b n) = n + i`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
    [ASM_SIMP_TAC[INLINE_MIN_LE_L]; ALL_TAC]) THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) &&
       can (find_term (fun t -> try fst(dest_const t) = "bytes8" with Failure _ -> false)) (concl th)
    then MP_TAC(SPEC `n + i` th) THEN (ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC])
    else NO_TAC);;


let INLINE_ZSTEP_EQ_TAC =
  SUBGOAL_THEN `i + 1 = inline_zsteps b n` ASSUME_TAC THENL
   [INLINE_ARITH_WITH [`i < inline_zsteps b n`; `~(i + 1 < inline_zsteps b n)`]; ALL_TAC];;

let INLINE_ZBODY_B_TAC exec =
  INLINE_ZSTEP_EQ_TAC THEN
  STRIP_ASSUME_TAC(MATCH_MP (SPECL [`b:num->byte`;`n:num`;`i:num`] INLINE_ZSTEPS_OK)
    (end_itlist CONJ (map ASSUME [`n < 80`; `i + 1 = inline_zsteps b n`;
       `forall j. n <= j /\ j < 80 ==> (b:num->byte) j = word 0`]))) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `i + 1 = inline_zsteps b n`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `(b:num->byte) (n + i) = word 0`]) THEN
  ASSUME_TAC(MATCH_MP (SPECL [`b:num->byte`;`n:num`] INLINE_ZRUN_OK)
    (CONJ (ASSUME `n < 80`) (ASSUME `forall j. n <= j /\ j < 80 ==> (b:num->byte) j = word 0`))) THEN
  ARM_STEPS_TAC exec (1--5) THEN
  MP_TAC(SPEC `n + i` INLINE_ZB_PC) THEN (ANTS_TAC THENL [INLINE_ARITH_WITH [`n + i < 80`]; DISCH_TAC]) THEN
  SUBGOAL_THEN `(n + i = 79) <=> T` ASSUME_TAC THENL [REWRITE_TAC[] THEN INLINE_ARITH_WITH [`n + i + 1 = 80`]; ALL_TAC] THEN
  SUBGOAL_THEN `MIN (n + i + 1) (inline_zrun b n) = 80` ASSUME_TAC THENL
   [INLINE_ARITH_WITH [`n + i + 1 = 80`; `inline_zrun b n = 80`]; ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC;;

let INLINE_ZBODY_C_TAC exec =
  INLINE_ZSTEP_EQ_TAC THEN
  ASSUME_TAC(MATCH_MP (SPECL [`b:num->byte`;`n:num`;`i:num`] INLINE_ZSTEPS_FAIL)
    (end_itlist CONJ (map ASSUME [`n < 80`; `i + 1 = inline_zsteps b n`;
       `~(forall j. n <= j /\ j < 80 ==> (b:num->byte) j = word 0)`]))) THEN
  ASSUME_TAC(MATCH_MP (SPECL [`b:num->byte`;`n:num`;`i:num`] INLINE_ZRUN_FAIL)
    (end_itlist CONJ (map ASSUME [`n < 80`; `i + 1 = inline_zsteps b n`;
       `~(forall j. n <= j /\ j < 80 ==> (b:num->byte) j = word 0)`]))) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `i + 1 = inline_zsteps b n`)) THEN
  ARM_STEPS_TAC exec (1--2) THEN
  MP_TAC(SPEC `(b:num->byte) (n + i)` INLINE_ZB_EQ0) THEN
  (ASM_REWRITE_TAC[] THEN DISCH_TAC) THEN
  SUBGOAL_THEN `MIN (n + i + 1) (inline_zrun b n) = n + i` ASSUME_TAC THENL
   [INLINE_ARITH_WITH [`inline_zrun b n = n + i`]; ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC;;

let INLINE_ZBODY_A_TAC exec =
  MP_TAC(SPECL [`b:num->byte`;`n:num`;`i:num`] INLINE_ZSTEPS_MID) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `(b:num->byte) (n + i) = word 0`]) THEN
  MP_TAC(SPECL [`b:num->byte`;`n:num`;`i + 1`] INLINE_ZSTEPS_LT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ARM_STEPS_TAC exec (1--5) THEN
  SUBGOAL_THEN `~(n + i = 79)` ASSUME_TAC THENL [INLINE_ARITH_WITH [`n + i + 1 < 80`]; ALL_TAC] THEN
  MP_TAC(SPEC `n + i` INLINE_ZB_PC) THEN (ANTS_TAC THENL [INLINE_ARITH_WITH [`n + i < 80`]; DISCH_TAC]) THEN
  SUBGOAL_THEN `MIN (n + i + 1) (inline_zrun b n) = n + i + 1` ASSUME_TAC THENL [MATCH_MP_TAC INLINE_MIN_LE_L THEN INLINE_ARITH_WITH [`n + (i + 1) <= inline_zrun b n`]; ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC;;

let INLINE_ZBODY_TAC exec =
  INLINE_ZBODY_PREP_TAC THEN
  ASM_CASES_TAC `i + 1 < inline_zsteps b n` THENL
   [INLINE_ZBODY_A_TAC exec THENL [CONV_TAC WORD_RULE; PATH_DISCHARGE_TAC]; ALL_TAC] THEN
  ASM_CASES_TAC `forall j. n <= j /\ j < 80 ==> (b:num->byte) j = word 0` THENL
   [INLINE_ZBODY_B_TAC exec THENL
     [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN INLINE_ARITH_WITH [`n + i + 1 = 80`]; PATH_DISCHARGE_TAC];
    INLINE_ZBODY_C_TAC exec THENL
     [AP_TERM_TAC THEN ARITH_TAC; PATH_DISCHARGE_TAC]];;

let INLINE_ZEXIT_TAC =
  REWRITE_TAC[LT_REFL] THEN FULL_INIT_TAC THEN
  MP_TAC(SPECL [`b:num->byte`;`n:num`] INLINE_ZRUN_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_FINAL_STATE_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    ASSUME_TAC(MATCH_MP (SPECL [`b:num->byte`;`n:num`] INLINE_ZRUN_OK)
      (CONJ (ASSUME `n < 80`) (ASSUME `forall j. n <= j /\ j < 80 ==> (b:num->byte) j = word 0`))) THEN
    ASM_REWRITE_TAC[INLINE_ZSTEPS] THEN AP_TERM_TAC THEN INLINE_ARITH_WITH [`n < 80`];
    EXISTS_TAC `e2:(uarch_event)list` THEN ASM_REWRITE_TAC[APPEND]];;

let INLINE_ZCHK_LOOP mc exec loop exit fail (rs:string list) =
  let r k = List.nth rs k in
  let tm = INLINE_ZCHK_LOOP_TERM mc loop exit fail rs in
  let inv = parse_term(Printf.sprintf
   "\\p s. aligned_bytes_loaded s (word pc) %s /\\
          read %s s = sg /\\ read %s s = word(MIN (n + p) (inline_zrun b n)) /\\
          (!j. j < 80 ==> read(memory :> bytes8(word_add sg (word j))) s = b j) /\\
          read PC s = word(if p < inline_zsteps b n then pc + %s
                           else if (!j. n <= j /\\ j < 80 ==> b j = word 0)
                                then pc + %s else pc + %s)"
   mc (r 1) (r 2) loop exit fail) in
  prove(tm, INLINE_ZSTART_TAC exec INLINE_ZTPL inv THENL
    [INLINE_ZINIT_TAC; INLINE_ZBODY_TAC exec; INLINE_ZEXIT_TAC]);;

(* The instances: (function, head label, exit label, failure label,          *)
(* registers [R0; R1; R2]); the labels are those of the layout, with the     *)
(* function name as prefix, e.g. mldsa44_verify_internal_loop11.             *)
let INLINE_ZCHK_LOOP_INSTANCES =
 [("mldsa44_verify_internal","loop11","join7","join2",["X8";"X26";"X21"])];;

(* NOT YET DONE: the instances of 65 and 87,                                 *)
(*   ("mldsa65_verify_internal","loop12","join7","join2",["X8";"X27";"X24"]) *)
(*   ("mldsa87_verify_internal","loop14","join7","join2",["X8";"X27";"X24"]) *)
(* have the same code with omega = 55 and 75 instead of 80: the compare is   *)
(* with 0x37 and 0x4b, so that the constants 80 and 18446744073709551537     *)
(* (= 2^64 - 79, from x21 + 1 - 80) of the statement, of inline_zrun,        *)
(* inline_zsteps, INLINE_ZB_PC and of the tactics have to become omega and   *)
(* 2^64 - (omega - 1), as a parameter of the generator. The proof is         *)
(* otherwise the same (the ldrb, cbnz, add, cmp, b.ne are identical).        *)

let INLINE_ZCHK_LOOP_OF (fn,loop,exit,fail,rs) =
  let mc = "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc" in
  let l x = fn ^ "_" ^ x in
  INLINE_ZCHK_LOOP mc (INLINE_LOOP_EXEC (l loop) (l exit)) (l loop) (l exit) (l fail) rs;;

(* ------------------------------------------------------------------------- *)
(* Shapes 54 and 53: the loop of mld_unpack_hints over the hints j = s + 1,  *)
(* ..., with the two exits: the statement INLINE_HUNP_LOOP_TERM, the         *)
(* definitions, the lemmas on the iterations and the tactics of one          *)
(* iteration; INLINE_HUNP_LOOP at the end of the file is the theorem for     *)
(* the instance of mldsa44_verify_internal.                                  *)
(* Registers (mldsa44_verify_internal, head loop13 = +0x24c0):               *)
(*   R0 = x9 = j (= s + 1 at the head), R1 = x10 = P + j, R2 = x13 = 1,       *)
(*   R3 = x27 = h, R4 = x11, R7 = x12 temporaries, R5 = x21 = w (= new),     *)
(*   R6 = x8 = s (= old)                                                     *)
(* The exec range is from join9 (+0x24ac) to +0x24dc, the exits are join6    *)
(* (ok, x9 = w) and loop13_exit2 (+0x24d8, P[j] <= P[j - 1]).                *)
(* The proof is one loop over inline_hsteps iterations with a PC-dependent   *)
(* invariant as for INLINE_ZCHK_LOOP: A (continue, 11 instructions), B (last *)
(* iteration, exit join6), C (failing iteration, 6 instructions), as         *)
(* INLINE_HBODY_A_TAC, INLINE_HBODY_B_TAC and INLINE_HBODY_C_TAC, and the    *)
(* exit INLINE_HEXIT_TAC. The store h[P[j]] := 1 is at a symbolic offset:    *)
(* INLINE_HFRAME_PREP_TAC keeps the other words of h across it and           *)
(* INLINE_HFRAME_TAC proves the frame with the bound val P[j] < 256.         *)
(* ------------------------------------------------------------------------- *)
(* The run of the second hint loop *)
let INLINE_HRUN = new_definition
 `inline_hrun (b:num->byte) s w =
    minimal j. s < j /\ (j = w \/ val(b j) <= val(b(j - 1)))`;;

let INLINE_HSTEPS = new_definition
 `inline_hsteps (b:num->byte) s w =
    if inline_hrun b s w = w then w - s - 1 else inline_hrun b s w - s`;;

let INLINE_HRUN_FACTS = prove
 (`!(b:num->byte) s w.
     s + 1 < w
     ==> s < inline_hrun b s w /\ inline_hrun b s w <= w /\
         (inline_hrun b s w = w \/
          val(b(inline_hrun b s w)) <= val(b(inline_hrun b s w - 1))) /\
         (!j. s < j /\ j < inline_hrun b s w
              ==> val(b(j - 1)) < val(b j)) /\
         ((!j. s < j /\ j < w ==> val(b(j - 1)) < val(b j)) <=>
          inline_hrun b s w = w)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `?j. s < j /\ (j = w \/ val((b:num->byte) j) <= val(b(j - 1)))`
   (fun th -> MP_TAC(MATCH_MP (fst(EQ_IMP_RULE(REWRITE_RULE[GSYM INLINE_HRUN] (BETA_RULE
     (SPEC `\j. s < j /\ (j = w \/ val((b:num->byte) j) <= val(b(j - 1)))` MINIMAL))))) th)) THENL
   [EXISTS_TAC `w:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `m = inline_hrun (b:num->byte) s w` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `m <= w` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:num` o check (fun th -> is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!j. s < j /\ j < m ==> val((b:num->byte)(j - 1)) < val(b j)` ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(j:num = w)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THENL
   [DISCH_TAC THEN ASM_CASES_TAC `m:num = w` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th))) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(SPEC `m:num` (ASSUME `!j. s < j /\ j < w ==> val((b:num->byte)(j - 1)) < val(b j)`)) THEN
    (ANTS_TAC THENL [INLINE_ARITH_WITH [`s < m`; `m <= w`; `~(m:num = w)`]; ALL_TAC]) THEN
    ASM_ARITH_TAC;
    DISCH_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check(fun th -> is_forall(concl th) && free_in `m:num` (concl th) && not(free_in `m':num` (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let INLINE_HFACTS_TAC =
  REWRITE_TAC[INLINE_HSTEPS] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b:num->byte`;`s:num`;`w:num`] INLINE_HRUN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `m = inline_hrun (b:num->byte) s w` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `m:num = w` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ASM_REWRITE_TAC[];;

let INLINE_HSTEPS_POS = prove
 (`!(b:num->byte) s w. s + 1 < w ==> 0 < inline_hsteps b s w`,
  REPEAT GEN_TAC THEN INLINE_HFACTS_TAC THEN ASM_ARITH_TAC);;

let INLINE_HSTEPS_LT = prove
 (`!(b:num->byte) s w i. s + 1 < w /\ i < inline_hsteps b s w
        ==> s + 1 + i < w /\ s + 1 + i <= inline_hrun b s w`,
  REPEAT GEN_TAC THEN INLINE_HFACTS_TAC THEN ASM_ARITH_TAC);;

let INLINE_HSTEPS_MID = prove
 (`!(b:num->byte) s w i. s + 1 < w /\ i + 1 < inline_hsteps b s w
        ==> val(b(s + i)) < val(b(s + 1 + i)) /\ s + 1 + i + 1 < w`,
  REPEAT GEN_TAC THEN INLINE_HFACTS_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s + 1 + i` o check (fun th -> is_forall(concl th))) THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  REWRITE_TAC[ARITH_RULE `(s + 1 + i) - 1 = s + i`] THEN ASM_ARITH_TAC);;

let INLINE_HSTEPS_OK = prove
 (`!(b:num->byte) s w i. s + 1 < w /\ i + 1 = inline_hsteps b s w /\
                         inline_hrun b s w = w
        ==> val(b(s + i)) < val(b(s + 1 + i)) /\ s + 1 + i + 1 = w`,
  REPEAT GEN_TAC THEN INLINE_HFACTS_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s + 1 + i` o check (fun th -> is_forall(concl th))) THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  REWRITE_TAC[ARITH_RULE `(s + 1 + i) - 1 = s + i`] THEN ASM_ARITH_TAC);;

let INLINE_HSTEPS_FAIL = prove
 (`!(b:num->byte) s w i. s + 1 < w /\ i + 1 = inline_hsteps b s w /\
                         ~(inline_hrun b s w = w)
        ==> val(b(s + 1 + i)) <= val(b(s + i)) /\ inline_hrun b s w = s + 1 + i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INLINE_HSTEPS] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b:num->byte`;`s:num`;`w:num`] INLINE_HRUN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `m = inline_hrun (b:num->byte) s w` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(m:num = w)`]) THEN
  (SUBGOAL_THEN `m = s + 1 + i` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `m = s + 1 + i`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `(s + 1 + i) - 1 = s + i`]) THEN
  ASM_REWRITE_TAC[]);;

let INLINE_HSET = new_definition
 `inline_hset (x:num->int32) (b:num->byte) s k q =
    if ?j. s < j /\ j < k /\ val(b j) = q then word 1 else x q`;;

let INLINE_HEXEC = INLINE_LOOP_EXEC "mldsa44_verify_internal_loop13" "mldsa44_verify_internal_in_sig_unpack_hints_part2_end";;

let INLINE_HUNP_LOOP_TERM mc loop exit1 exit2 (rs:string list) =
  let r k = List.nth rs k in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e a h (b:num->byte) (x:num->int32) s w pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        s + 1 < w /\\ w <= 80 /\\
        ALL (nonoverlapping (h,1024)) [(word pc,libmldsa_size); (a,80)]
        ==> ensures arm
             (\\s'. aligned_bytes_loaded s' (word pc) %s /\\
                  read PC s' = word (pc + %s) /\\
                  read %s s' = word (s + 1) /\\
                  read %s s' = word_add a (word (s + 1)) /\\
                  read %s s' = word 1 /\\ read %s s' = h /\\
                  read %s s' = word w /\\ read %s s' = word s /\\
                  (!j. j < 80
                       ==> read(memory :> bytes8(word_add a (word j))) s' = b j) /\\
                  (!q. q < 256
                       ==> read(memory :> bytes32(word_add h (word(4 * q)))) s' =
                           x q) /\\
                  read events s' = e)
             (\\s'. read PC s' = word (if inline_hrun b s w = w
                                      then pc + %s else pc + %s) /\\
                  read %s s' = word (inline_hrun b s w) /\\
                  read %s s' = word_add a (word (inline_hrun b s w)) /\\
                  (!q. q < 256
                       ==> read(memory :> bytes32(word_add h (word(4 * q)))) s' =
                           inline_hset x b s (inline_hrun b s w) q) /\\
                  (exists e2.
                     read events s' = APPEND e2 e /\\
                     e2 = f_events b s w a h pc /\\
                     memaccess_inbounds e2 [a,80] [h,1024]))
             (MAYCHANGE [PC; %s; %s; %s; %s] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(h,1024)])"
   mc loop (r 0) (r 1) (r 2) (r 3) (r 5) (r 6) exit1 exit2 (r 0) (r 1)
   (r 0) (r 1) (r 4) (r 7));;

let INLINE_HTM = INLINE_HUNP_LOOP_TERM "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc" "mldsa44_verify_internal_loop13" "mldsa44_verify_internal_join6" "mldsa44_verify_internal_loop13_exit2" ["X9";"X10";"X13";"X27";"X11";"X21";"X8";"X12"];;

let INLINE_HEXEC = INLINE_LOOP_EXEC "mldsa44_verify_internal_join9" "mldsa44_verify_internal_in_sig_unpack_hints_part2_end";;

let INLINE_HSET_0 = prove
 (`!(x:num->int32) (b:num->byte) s k q. k <= s + 1 ==> inline_hset x b s k q = x q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INLINE_HSET] THEN
  SUBGOAL_THEN `~(?j. s < j /\ j < k /\ val((b:num->byte) j) = q)` (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `j:num` THEN ASM_ARITH_TAC);;

let INLINE_HSET_ADD1 = prove
 (`!(x:num->int32) (b:num->byte) s k q.
     inline_hset x b s (k + 1) q =
     if s < k /\ val(b k) = q then word 1 else inline_hset x b s k q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INLINE_HSET] THEN
  SUBGOAL_THEN `(?j. s < j /\ j < k + 1 /\ val((b:num->byte) j) = q) <=>
                (s < k /\ val(b k) = q) \/ (?j. s < j /\ j < k /\ val(b j) = q)` SUBST1_TAC THENL
   [EQ_TAC THENL
     [STRIP_TAC THEN ASM_CASES_TAC `j:num = k` THENL
       [DISJ1_TAC THEN ASM_MESON_TAC[]; DISJ2_TAC THEN EXISTS_TAC `j:num` THEN ASM_ARITH_TAC];
      STRIP_TAC THENL
       [EXISTS_TAC `k:num` THEN ASM_ARITH_TAC;
        EXISTS_TAC `j:num` THEN ASM_ARITH_TAC]];
    ALL_TAC] THEN
  ASM_CASES_TAC `s < k /\ val((b:num->byte) k) = q` THEN ASM_REWRITE_TAC[]);;

let INLINE_HTPL = `\(b:num->byte) (s:num) (w:num) (a:int64) (h:int64) (pc:num).
   APPEND ([]:(uarch_event)list)
    (APPEND (ENUMERATEL (inline_hsteps b s w)
       (\i. if i + 1 < inline_hsteps b s w then f_ev_a b s w a h pc i
            else if inline_hrun b s w = w
                 then f_ev_ok b s w a h pc i else f_ev_fail b s w a h pc i))
      ([]:(uarch_event)list))`;;

let INLINE_HINV = `\i s'. aligned_bytes_loaded s' (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
      read X9 s' = word(MIN (s + 1 + i) (inline_hrun b s w)) /\
      read X10 s' = word_add a (word(MIN (s + 1 + i) (inline_hrun b s w))) /\
      read X13 s' = word 1 /\ read X27 s' = h /\ read X21 s' = word w /\ read X8 s' = word s /\
      (!j. j < 80 ==> read(memory :> bytes8(word_add a (word j))) s' = b j) /\
      (!q. q < 256 ==> read(memory :> bytes32(word_add h (word(4 * q)))) s' =
           inline_hset x b s (MIN (s + 1 + i) (inline_hrun b s w)) q) /\
      read PC s' = word(if i < inline_hsteps b s w then pc + 52780
                       else if inline_hrun b s w = w then pc + 52536 else pc + 52804)`;;

let INLINE_HSTART_TAC =
  CONCRETIZE_F_EVENTS_TAC INLINE_HTPL THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `h:int64`; `b:num->byte`; `x:num->int32`; `s:num`; `w:num`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; fst INLINE_HEXEC; NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  GLUE_EVENTS_WHILE_TAC `inline_hsteps (b:num->byte) s w` INLINE_HINV THEN REPEAT CONJ_TAC;;

let INLINE_HINIT_TAC =
  MP_TAC(SPECL [`b:num->byte`;`s:num`;`w:num`] INLINE_HSTEPS_POS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`b:num->byte`;`s:num`;`w:num`] INLINE_HRUN_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  (SUBGOAL_THEN `MIN (s + 1 + 0) (inline_hrun b s w) = s + 1` (fun th -> REWRITE_TAC[th]) THENL
    [INLINE_ARITH_WITH [`s < inline_hrun b s w`]; ALL_TAC]) THEN
  FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[ADD_0; ENUMERATEL; APPEND] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `q:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`x:num->int32`;`b:num->byte`;`s:num`;`s + 1`;`q:num`] INLINE_HSET_0) THEN
    REWRITE_TAC[LE_REFL] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `q:num` o check (fun th -> is_forall(concl th) && free_in `x:num->int32` (concl th))) THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `[]:(uarch_event)list` THEN REWRITE_TAC[APPEND_NIL;APPEND] THEN
    DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC];;

let INLINE_HADDR = prove
 (`!(a:int64) s i. word_add (word_add a (word (s + 1 + i))) (word 18446744073709551615) =
                   word_add a (word (s + i))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `word (s + 1 + i):int64 = word_add (word (s + i)) (word 1)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`word (s + i):int64`,`y:int64`) THEN CONV_TAC WORD_ARITH);;

let INLINE_HADDR2 = prove(`!s i. word ((s + 1 + i) + 18446744073709551615):int64 = word (s + i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `(s + 1 + i) + 18446744073709551615 = 1 * 18446744073709551616 + (s + i)`; MOD_MULT_ADD]);;

let INLINE_HBODY_PREP_TAC =
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  MP_TAC(SPECL [`b:num->byte`;`s:num`;`w:num`;`i:num`] INLINE_HSTEPS_LT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  (SUBGOAL_THEN `MIN (s + 1 + i) (inline_hrun b s w) = s + 1 + i`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
    [MATCH_MP_TAC INLINE_MIN_LE_L THEN INLINE_ARITH_WITH [`s + 1 + i <= inline_hrun b s w`]; ALL_TAC]) THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) &&
       can (find_term (fun t -> try fst(dest_const t) = "bytes8" with Failure _ -> false)) (concl th)
    then
      MP_TAC(SPEC `s + 1 + i` th) THEN (ANTS_TAC THENL [INLINE_ARITH_WITH [`s + 1 + i < w`; `w <= 80`]; DISCH_TAC]) THEN
      MP_TAC(SPEC `s + i` th) THEN (ANTS_TAC THENL [INLINE_ARITH_WITH [`s + 1 + i < w`; `w <= 80`]; ALL_TAC]) THEN
      DISCH_THEN(fun th2 -> ASSUME_TAC th2 THEN
        SUBGOAL_THEN `read (memory :> bytes8 (word_add (word_add a (word (s + 1 + i))) (word 18446744073709551615))) s0 = (b:num->byte) (s + i)` ASSUME_TAC THENL
         [REWRITE_TAC[INLINE_HADDR] THEN ACCEPT_TAC th2; ALL_TAC] THEN
        SUBGOAL_THEN `read (memory :> bytes8 (word_add a (word ((s + 1 + i) + 18446744073709551615)))) s0 = (b:num->byte) (s + i)` ASSUME_TAC THENL
         [REWRITE_TAC[INLINE_HADDR2] THEN ACCEPT_TAC th2; ALL_TAC])
    else NO_TAC);;

let INLINE_HL_CMP = prove
 (`!s j. s < j /\ j < 2 EXP 64
         ==> (val(word s:int64) <= val(word j:int64) <=> T) /\
             (val(word_sub (word j:int64) (word s)) = 0 <=> F)`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    SUBGOAL_THEN `s < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(word j:int64) = word ((j - s) + s)` SUBST1_TAC THENL
   [AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_SUB_ADD] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `j - s < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN ASM_ARITH_TAC);;

(*** Rewrite the other assumptions with the facts of a conjunction of     ***)
(*** equivalences, which is the first assumption                          ***)
let INLINE_REWRITE_ASSUMS_WITH_TOP =
  FIRST_X_ASSUM(fun th ->
    if is_conj(concl th) then RULE_ASSUM_TAC(REWRITE_RULE(CONJUNCTS th))
    else NO_TAC);;


let INLINE_HL_HI = prove
 (`!(x:byte) (y:byte).
    (&(val (word_zx (word_zx (word_zx x:int32):int64):int32)) -
     &(val (word_zx (word_zx (word_zx y:int32):int64):int32)) : int =
     &(val (word_sub (word_zx (word_zx (word_zx x:int32):int64):int32)
                     (word_zx (word_zx (word_zx y:int32):int64):int32))) /\
     ~(val (word_sub (word_zx (word_zx (word_zx x:int32):int64):int32)
                     (word_zx (word_zx (word_zx y:int32):int64):int32)) = 0))
    <=> val y < val x`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

(*** Rewrite the assumptions with the truth value of the assumption t or ~t ***)
let INLINE_RW_ASSUMS_BY t =
  FIRST_X_ASSUM(fun th ->
    if concl th = t then RULE_ASSUM_TAC(REWRITE_RULE[EQT_INTRO th]) THEN ASSUME_TAC th
    else if concl th = mk_neg t then RULE_ASSUM_TAC(REWRITE_RULE[EQF_INTRO th]) THEN ASSUME_TAC th
    else NO_TAC);;

let INLINE_HSIM_HEAD_TAC =
  MP_TAC(SPECL [`s:num`;`s + 1 + i`] INLINE_HL_CMP) THEN
  (ANTS_TAC THENL [INLINE_ARITH_WITH [`s + 1 + i < w`; `w <= 80`]; DISCH_TAC]) THEN
  ARM_STEPS_TAC INLINE_HEXEC (1--3) THEN INLINE_REWRITE_ASSUMS_WITH_TOP THEN
  ARM_STEPS_TAC INLINE_HEXEC (4--6) THEN
  MP_TAC(SPECL [`(b:num->byte)(s + 1 + i)`;`(b:num->byte)(s + i)`] INLINE_HL_HI) THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]));;

let INLINE_HL_ZX = prove(`!x:byte. word_zx (word_zx x:int32):int64 = word (val x)`,
  GEN_TAC THEN BITBLAST_TAC);;
let INLINE_HL_VAL256 = prove(`!x:byte. val x < 256`, GEN_TAC THEN MP_TAC(ISPEC `x:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV);;
let INLINE_HL_VALW = prove(`!x:byte. val(word (val x):int64) = val x`, GEN_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN MP_TAC(SPEC `x:byte` INLINE_HL_VAL256) THEN ARITH_TAC);;

let INLINE_HSTORE_PREP_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[INLINE_HL_ZX]) THEN
  ASSUME_TAC(SPEC `(b:num->byte)(s + 1 + i)` INLINE_HL_VAL256) THEN
  ASSUME_TAC(SPEC `(b:num->byte)(s + 1 + i)` INLINE_HL_VALW);;

let INLINE_HFRAME_PREP_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `!q. q < 256 ==> read (memory :> bytes32 (word_add h (word (4 * q)))) s0 = (f:num->int32) q`) (concl th)
    then
      SUBGOAL_THEN `!q. q < 256 /\ ~(q = val((b:num->byte)(s + 1 + i)))
                        ==> read (memory :> bytes32 (word_add h (word (4 * q)))) s0 =
                            inline_hset x b s (s + 1 + i) q` ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN MP_TAC(SPEC `q:num` th) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
        ALL_TAC]
    else NO_TAC);;

let INLINE_HL_EQ = prove
 (`!w k. k + 1 <= w /\ w < 2 EXP 64
         ==> (val(word_sub (word w:int64) (word_add (word k) (word 1))) = 0 <=> k + 1 = w)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_add (word k:int64) (word 1) = word (k + 1)` SUBST1_TAC THENL
   [REWRITE_TAC[WORD_ADD]; ALL_TAC] THEN
  SUBGOAL_THEN `(word w:int64) = word ((w - (k + 1)) + (k + 1))` SUBST1_TAC THENL
   [AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_SUB_ADD; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `w - (k + 1) < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN ASM_ARITH_TAC);;

let INLINE_HA_MEM_TAC =
  X_GEN_TAC `q:num` THEN DISCH_TAC THEN
  REWRITE_TAC[ARITH_RULE `s + 1 + i + 1 = (s + 1 + i) + 1`; INLINE_HSET_ADD1] THEN
  ASM_CASES_TAC `val((b:num->byte)(s + 1 + i)) = q` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    ASM_REWRITE_TAC[ARITH_RULE `s < s + 1 + i`];
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) && free_in `inline_hset` (concl th) && is_imp(snd(dest_forall(concl th)))
         && is_conj(lhand(snd(dest_forall(concl th))))
      then MATCH_MP_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN ASM_REWRITE_TAC[]];;

let INLINE_HL_ADDR = prove
 (`!(a:int64) k. word_add (word_add a (word k)) (word 1) = word_add a (word (k + 1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

(*** The frame: the store at the byte index, within the 1024 bytes of h ***)
let INLINE_HFRAME_TAC =
  let isv t =
    try fst(dest_const(rator t)) = "val" && type_of(rand t) = `:byte`
    with Failure _ -> false in
  W(fun (asl,w) ->
    let s0,s1 = rand(rator w),rand w in
    let ok th =
      let c = concl th in
      try is_comb c && rand(rator c) = s0 && rand c = s1 &&
          can (find_term (fun t -> try fst(dest_const t) = "MAYCHANGE" with Failure _ -> false)) c
      with Failure _ -> false in
    let th = snd(find (fun (_,th) -> ok th) asl) in
    let vs = setify(find_terms isv (concl th)) in
    MP_TAC th THEN
    MAP_EVERY (fun t -> MP_TAC(SPEC (rand t) INLINE_HL_VAL256)) vs THEN
    MAP_EVERY (fun t -> SPEC_TAC(t,genvar `:num`)) vs THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN MONOTONE_MAYCHANGE_TAC);;

(* ------------------------------------------------------------------------- *)
(* The assembled proof of INLINE_HUNP_LOOP (the loop of shapes 53/54 in      *)
(* mldsa44_verify_internal): the three paths of an iteration (A: the next    *)
(* hint is larger, the loop goes on; B: the same at the last hint, exit at   *)
(* join6; C: the hints are not increasing, exit at loop13_exit2) and the     *)
(* exit. The store of the hint, h[P[j]] := 1, is at h + 4 * val(P[j]),       *)
(* within the 1024 bytes of h as val(P[j]) < 256.                            *)
(* ------------------------------------------------------------------------- *)

let INLINE_HSTORE_NONOV_TAC =
  SUBGOAL_THEN
   `nonoverlapping (word_add h (word (4 * val ((b:num->byte) (s + 1 + i)))):int64,4)
                   (word pc,libmldsa_size)` ASSUME_TAC THENL
   [NONOVERLAPPING_TAC; ALL_TAC];;

let INLINE_HCMP_PC_TAC =
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) then NO_TAC else
    if concl th = `val((b:num->byte)(s + i)) < val(b(s + 1 + i))`
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th else NO_TAC);;

let INLINE_HSTORE_STEPS_TAC =
  ARM_STEPS_TAC INLINE_HEXEC (7--8) THEN INLINE_HSTORE_NONOV_TAC THEN
  ARM_STEPS_TAC INLINE_HEXEC (9--11);;

let INLINE_HFINAL_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  FIRST [CONV_TAC WORD_RULE THEN NO_TAC;
         INLINE_HA_MEM_TAC THEN NO_TAC;
         REWRITE_TAC[GSYM ADD_ASSOC] THEN ASM_REWRITE_TAC[] THEN NO_TAC;
         REWRITE_TAC[INLINE_HADDR] THEN GLUE_PATH_DISCHARGE_TAC THEN NO_TAC;
         INLINE_HFRAME_TAC];;

let INLINE_HBODY_A_TAC =
  MP_TAC(SPECL [`b:num->byte`;`s:num`;`w:num`;`i:num`] INLINE_HSTEPS_MID) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  INLINE_HFRAME_PREP_TAC THEN
  INLINE_HSIM_HEAD_TAC THEN INLINE_HSTORE_PREP_TAC THEN INLINE_HCMP_PC_TAC THEN
  INLINE_HSTORE_STEPS_TAC THEN
  MP_TAC(SPECL [`b:num->byte`;`s:num`;`w:num`;`i + 1`] INLINE_HSTEPS_LT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`w:num`; `s + 1 + i`] INLINE_HL_EQ) THEN
  ANTS_TAC THENL [INLINE_ARITH_WITH [`s + 1 + i < w`; `w <= 80`]; DISCH_TAC] THEN
  SUBGOAL_THEN `~(s + 1 + i + 1 = w)` ASSUME_TAC THENL
   [INLINE_ARITH_WITH [`s + 1 + i + 1 < w`]; ALL_TAC] THEN
  SUBGOAL_THEN `MIN (s + 1 + i + 1) (inline_hrun b s w) = s + 1 + i + 1`
   (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC INLINE_MIN_LE_L THEN
    INLINE_ARITH_WITH [`s + 1 + (i + 1) <= inline_hrun b s w`]; ALL_TAC] THEN
  INLINE_HFINAL_TAC;;

let INLINE_HB_W_TAC =
  REWRITE_TAC[ARITH_RULE `MIN (w:num) w = w`] THEN
  SUBGOAL_THEN `w = s + 1 + i + 1` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC];;

let INLINE_HBODY_B_TAC =
  MP_TAC(SPECL [`b:num->byte`;`s:num`;`w:num`;`i:num`] INLINE_HSTEPS_OK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    concl th = `i + 1 = inline_hsteps b s w`)) THEN
  INLINE_HFRAME_PREP_TAC THEN
  INLINE_HSIM_HEAD_TAC THEN INLINE_HSTORE_PREP_TAC THEN INLINE_HCMP_PC_TAC THEN
  INLINE_HSTORE_STEPS_TAC THEN
  MP_TAC(SPECL [`w:num`; `s + 1 + i`] INLINE_HL_EQ) THEN
  ANTS_TAC THENL [INLINE_ARITH_WITH [`s + 1 + i < w`; `w <= 80`]; DISCH_TAC] THEN
  SUBGOAL_THEN `MIN (s + 1 + i + 1) (inline_hrun b s w) = w`
   (fun th -> REWRITE_TAC[th]) THENL
   [INLINE_ARITH_WITH [`s + 1 + i + 1 = w`; `inline_hrun b s w = w`]; ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  FIRST [INLINE_HB_W_TAC THEN CONV_TAC WORD_RULE THEN NO_TAC;
         INLINE_HB_W_TAC THEN INLINE_HA_MEM_TAC THEN NO_TAC;
         SUBGOAL_THEN `s + 1 + i + 1 = w` ASSUME_TAC THENL
          [ASM_ARITH_TAC; ALL_TAC] THEN
         REWRITE_TAC[GSYM ADD_ASSOC] THEN ASM_REWRITE_TAC[] THEN NO_TAC;
         REWRITE_TAC[INLINE_HADDR] THEN GLUE_PATH_DISCHARGE_TAC THEN NO_TAC;
         INLINE_HFRAME_TAC];;

let INLINE_HBODY_C_TAC =
  MP_TAC(SPECL [`b:num->byte`;`s:num`;`w:num`;`i:num`] INLINE_HSTEPS_FAIL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    concl th = `i + 1 = inline_hsteps b s w`)) THEN
  INLINE_HSIM_HEAD_TAC THEN
  SUBGOAL_THEN `~(val((b:num->byte)(s + i)) < val(b(s + 1 + i)))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[ARITH_RULE `MIN (s + 1 + i + 1) (s + 1 + i) = s + 1 + i`] THEN
  REPEAT CONJ_TAC THEN
  FIRST [REWRITE_TAC[INLINE_HADDR] THEN GLUE_PATH_DISCHARGE_TAC THEN NO_TAC;
         MONOTONE_MAYCHANGE_TAC];;

let INLINE_HEXIT_TAC =
  REWRITE_TAC[LT_REFL] THEN FULL_INIT_TAC THEN
  SUBGOAL_THEN
   `MIN (s + 1 + inline_hsteps b s w) (inline_hrun b s w) = inline_hrun b s w`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[INLINE_HSTEPS] THEN
    MP_TAC(SPECL [`b:num->byte`;`s:num`;`w:num`] INLINE_HRUN_FACTS) THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `e2:(uarch_event)list` THEN ASM_REWRITE_TAC[APPEND];;

let INLINE_HUNP_LOOP = prove
 (INLINE_HTM,
  INLINE_HSTART_TAC THENL
   [INLINE_HINIT_TAC;
    INLINE_HBODY_PREP_TAC THEN
    ASM_CASES_TAC `i + 1 < inline_hsteps b s w` THENL
     [INLINE_HBODY_A_TAC;
      SUBGOAL_THEN `i + 1 = inline_hsteps b s w` ASSUME_TAC THENL
       [INLINE_ARITH_WITH [`i < inline_hsteps b s w`;
                           `~(i + 1 < inline_hsteps b s w)`]; ALL_TAC] THEN
      ASM_CASES_TAC `inline_hrun b s w = w` THENL
       [INLINE_HBODY_B_TAC; INLINE_HBODY_C_TAC]];
    INLINE_HEXIT_TAC]);;
