(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* A SHAKE256 with 64 bytes of output that clang 23 -O3 has inlined with its *)
(* input in the stack frame: c2 = H(mu || w1', 64) of                        *)
(* mldsa87_verify_internal, 1088 bytes at F + 11776 (mu, then the 1024      *)
(* bytes of w1'). The code is that of the SHAKE256 of pk                     *)
(* (inline_sign_shake_gen.ml) except that the input is read relative to SP   *)
(* and that the 7 middle blocks are a loop; the loop runs a fixed number of  *)
(* times, so the proof steps through it, and the instance (shake_inst) and   *)
(* the tactics of inline_sign_shake_gen.ml are used with the exec theorem of *)
(* this region and the f_events arguments (fp, pc). sh_calls are the steps   *)
(* of the bl of each block, counted through the loop.                        *)
(*                                                                           *)
(* The region goes from loop9_exit5 (in_shake256_init_2) to the first load  *)
(* of the compare of c2 with c~ (after_mldsa_keccakf1600_permute_23 + 0x90): *)
(* the state at F + 12864 is zeroed, the input is absorbed, padded and       *)
(* permuted, the first 64 bytes of the state are copied to F + 11648 and the *)
(* state is zeroed. The squeeze also sets x8 to 0, which the compare after   *)
(* the region uses (sh_post).                                                *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_shake_gen.ml";;

(*** The input at F + off ***)

let SHAKES_IN off =
  mk_comb(`word_add (fp:int64)`,mk_comb(`word:num->int64`,mk_small_numeral off));;

let INLINE_SHAKES_TERM p off stop =
  let fr = 240 + p.sh_a + 208 in
  parse_term(Printf.sprintf
 "exists f_events.
    forall e (fp:int64) PK pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 16 fp /\\
      nonoverlapping (word_sub fp (word 240),%d) (word pc,libmldsa_size)
      ==> ensures arm
           (\\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read PC s = word (pc + %d) /\\
                read SP s = fp /\\
                read (memory :> bytes(word_add fp (word %d),%d)) s = PK /\\
                read events s = e)
           (\\s. read PC s = word (pc + %d) /\\ %s
                read (memory :> bytes(word_add fp (word %d),64)) s =
                  num_of_bytelist(list_of_seq (mld_shake256_byte %d PK) 64) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events fp pc /\\
                   memaccess_inbounds e2
                    [word_add fp (word %d),%d; word_add fp (word %d),208;
                     word_add fp (word %d),64; word_sub fp (word 240),240;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192]
                    [word_add fp (word %d),208; word_add fp (word %d),64;
                     word_sub fp (word 240),240]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [%s] ,,
            MAYCHANGE [memory :> bytes(word_add fp (word %d),208);
                       memory :> bytes(word_add fp (word %d),64);
                       memory :> bytes(word_sub fp (word 240),240)])"
  fr (SHAKE_START p) off p.sh_pklen stop p.sh_post p.sh_t p.sh_pklen
  off p.sh_pklen p.sh_a p.sh_t p.sh_a p.sh_t p.sh_mods p.sh_a p.sh_t);;

(*** The exec theorem of the region, decoded once ***)

let SHAKES_EXEC_CACHE = ref [];;

let SHAKES_EXEC p stop =
  let key = (p.sh_fn,stop) in
  try assoc key (!SHAKES_EXEC_CACHE) with Failure _ ->
  let th =
    ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(SHAKE_START p,stop); layout_range "mldsa_keccakf1600_permute"] in
  SHAKES_EXEC_CACHE := (key,th) :: (!SHAKES_EXEC_CACHE); th;;

(*** The facts about the input at the start: its lanes (abbreviated as      ***)
(*** pkw<n> by SHAKE_PK_ABBREV_TAC), the lanes beyond it in the last block  ***)
(*** (zero) and the 16-byte chunks that the first block loads, as joins of  ***)
(*** two lanes; the addresses are normalized to F + k                       ***)

let SHAKES_INFACT p off =
  subst [SHAKES_IN off,`a:int64`; mk_small_numeral p.sh_pklen,`n:num`]
   `read (memory :> bytes(a,n)) s0 = PK`;;

let SHAKES_LANES_TAC p off =
  FIRST_ASSUM(fun th ->
    if concl th <> SHAKES_INFACT p off then NO_TAC else
    MAP_EVERY (fun i ->
      let k = mk_small_numeral(8 * i) in
      let th1 = SPECL [SHAKES_IN off; mk_small_numeral p.sh_pklen; `PK:num`; k;
                       `s0:armstate`] READ_MEMORY_BYTES64_OF_NUM in
      let th2 = MP th1 (CONJ th (EQT_ELIM(NUM_REDUCE_CONV(rand(lhand(concl th1)))))) in
      ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                  (REWRITE_RULE[WORD_ADD_0]
                    (CONV_RULE(DEPTH_CONV NUM_MULT_CONV) th2))))
     (0--(p.sh_pklen / 8 - 1)));;

let SHAKES_BOUND_TAC p off =
  let nb = mk_small_numeral(8 * p.sh_pklen) in
  FIRST_ASSUM(fun th ->
    if concl th <> SHAKES_INFACT p off then NO_TAC else
    let bth = CONV_RULE(DEPTH_CONV NUM_MULT_CONV)
               (MATCH_MP SHAKE_READ_BYTES_BOUND th) in
    MAP_EVERY (fun t ->
      let m = mk_small_numeral(8 * p.sh_pklen + 64 * t) in
      ASSUME_TAC(MP (SPECL [`PK:num`; nb; m] SHAKE_PK_HIGH)
                    (CONJ bth (EQT_ELIM(NUM_REDUCE_CONV
                       (mk_binop `(<=):num->num->bool` nb m))))))
     (0--(16 - SHAKE_REM p / 8)));;

let SHAKES_IN128_TAC off ks =
  W(fun (asl,w) ->
    let lanes = mapfilter (fun (_,a) ->
      let c = concl a in
      if is_eq c && can (term_match []
           `read (memory :> bytes64 (word_add fp (word k))) s0`) (lhs c)
      then a else fail()) asl in
    MAP_EVERY (fun k ->
      let tm = subst [SHAKES_IN(off + k),`a:int64`]
                 `read (memory :> bytes128 a) s0` in
      let th = CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV))
                (GEN_REWRITE_CONV I [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] tm) in
      ASSUME_TAC(REWRITE_RULE lanes th)) ks);;

(*** The call of the permutation in this region ***)

let SHAKES_CALL_TAC p stop =
  SHAKE_CALL_WITH_TAC (SHAKES_EXEC p stop) [`fp:int64`; `pc:num`];;

(* ------------------------------------------------------------------------- *)
(* The proof: block 0 with the zeroing of the state (the 16-byte loads of    *)
(* the input stored as 16-byte chunks at split0), the middle blocks, the     *)
(* last block with the padding, and the copy of the output.                  *)
(* ------------------------------------------------------------------------- *)

let INLINE_SHAKES_PROVE p off stop split0 =
  let c0 = hd p.sh_calls in
  let exec = SHAKES_EXEC p stop in
  let call = SHAKES_CALL_TAC p stop in
  prove
   (INLINE_SHAKES_TERM p off stop,
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600
     "H_PERM" THEN
    CONCRETIZE_F_EVENTS_TAC
     `\(fp:int64) (pc:num). f_ev_shs fp pc :(uarch_event)list` THEN
    META_EXISTS_TAC THEN
    REWRITE_TAC[NONOVERLAPPING_CLAUSES; fst exec] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    FULL_INIT_TAC THEN SHAKES_LANES_TAC p off THEN
    SHAKE_PK_ABBREV_TAC p THEN SHAKES_BOUND_TAC p off THEN
    SHAKES_IN128_TAC off split0 THEN
    MAP_EVERY (fun n -> ARM_STEPS_TAC exec [n] THEN SHAKE_SPLIT_TAC p)
     (1--c0) THEN
    SHAKE_SPLIT_STORES_TAC {p with sh_split = split0} (SHAKE_SV c0) THEN
    SHAKE_ASSEMBLE_TAC p (SHAKE_TA 0) (SHAKE_SV c0) THEN
    call (SHAKE_TA 0) (c0 + 1) THEN
    MAP_EVERY (SHAKE_BLOCK_WITH_TAC exec call p) (1--(SHAKE_NB p - 1)) THEN
    SHAKE_LAST_WITH_TAC exec call p THEN SHAKE_TAIL_WITH_TAC exec p);;

(* ------------------------------------------------------------------------- *)
(* The instance: c2 of mldsa87_verify_internal. The 8 blocks of 136 bytes    *)
(* end with the input, so the last block has only the padding (bytes 0 and  *)
(* 135 of the state).                                                        *)
(* ------------------------------------------------------------------------- *)

let SHAKES87_INST =
  { sh_fn = "mldsa87_verify_internal"; sh_start = "loop9_exit5";
    sh_stop = "";
    sh_pklen = 1088; sh_a = 12864; sh_t = 11648;
    sh_vars = ""; sh_pre = ""; sh_post = "read X8 s = word 0 /\\"; sh_reads = "";
    sh_mods = "X18; X19; X20; X21; X22; X23; X24; X25; X30";
    sh_calls = [66;140;215;290;365;440;515;590;611];
    sh_last_bytes = (0--7) @ (128--135); sh_last_chunks = [];
    sh_pk128 = []; sh_split = []; sh_rebuild = [0;128]; sh_steps = 648 };;

let SHAKES87_OFF = 11776;;

let SHAKES87_STOP =
  layout "mldsa87_verify_internal_after_mldsa_keccakf1600_permute_23" + 0x90;;

let SHAKES87_SPLIT0 = [0;16;32;48];;

let INLINE_SHAKES87_TERM =
  INLINE_SHAKES_TERM SHAKES87_INST SHAKES87_OFF SHAKES87_STOP;;

let INLINE_SHAKES87 () =
  INLINE_SHAKES_PROVE SHAKES87_INST SHAKES87_OFF SHAKES87_STOP SHAKES87_SPLIT0;;
