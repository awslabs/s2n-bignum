(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::SnappyDecompressor::DecompressAllTags<SnappyArrayWriter>: the     *)
(* lemmas, the cut points, the goals of the segments and their tactics, for  *)
(* the proof (statement in the spec file). The segment T is proved by the    *)
(* class of the tag byte, one job each (..._t_{b,s}_<class>_proof.ml); the   *)
(* proof file proves the others and the theorem.                             *)
(*                                                                           *)
(* Cut points (ENSURES_MEASURE_INDUCT, common/ensures_measure.ml) with the   *)
(* measure 2 * LENGTH rest (+ 1 at L, + 2 at the entry), rest the unread     *)
(* stream at ip in one of two states (DESIGN.md 7, 7e): the buffer (ip in    *)
(* the input, ip_limit_ = q + LENGTH inp, ip_limit_min_maxtaglen_ 4 below    *)
(* it, at least 5 bytes left) or scratch_ (ip = d + 41, at most 4 bytes, the *)
(* source empty):                                                            *)
(*                                                                           *)
(*  - E, the entry: the prologue and RefillTag (EMPTY with k = 0), then L or *)
(*    the exit;                                                              *)
(*  - L (loop1): DecompressBranchless (its tags as snappy_steps), then T, or *)
(*    RefillTag (WINDOW or EMPTY) and T or the exit;                         *)
(*  - T (join3): one tag of the slow path by kind (literal, long literal     *)
(*    with v = 240..252, copies with 1-, 2- and 4-byte offsets: memmove of   *)
(*    64 bytes or IncrementalCopy), then L directly or RefillTag and L, or   *)
(*    the exit.                                                              *)
(*                                                                           *)
(* The model at each cut point is snappy_decode_tags m inp [] =             *)
(* snappy_decode_tags m rest ob, ob the output so far at out. The frame of  *)
(* the segments is one footprint clause for all the memory written (so that *)
(* C ,, C = C), weakened to the frame of the statement at the end            *)
(* (FOOTPRINT_UNION_SUBSUMED_SEQ, MAYCHANGE_FOOTPRINT_MEMRANGE_SUBSUMED).     *)
(* The code is run one instruction at a time; branches on data are split   *)
(* and the cases that the arithmetic facts contradict are closed; the       *)
(* conditions of the others are kept as arithmetic.                        *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_snappy_array_writer_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_refill_tag_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/decompress_branchless_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/incremental_copy_spec.ml";;
needs "arm/proofs/snappy/array_writer.ml";;
needs "common/ensures_measure.ml";;
needs "arm/proofs/snappy/gcc12_O2/length_minus_offset_lib.ml";;
needs "common/snappy/snappy_slow_path.ml";;


(* Definitions for the proof of DecompressAllTags<SnappyArrayWriter>.       *)

let DAW_STMT = SNAPPY_DECOMPRESSOR_DECOMPRESS_ALL_TAGS_SNAPPY_ARRAY_WRITER_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
let daw_vars,daw_body = strip_forall DAW_STMT;;
let daw_hyp,daw_ens = dest_imp daw_body;;
let daw_P,daw_Q,daw_frame =
  match daw_ens with
    Comb(Comb(Comb(Comb(Const("ensures",_),_),p),q),c) -> p,q,c
  | _ -> failwith "daw_ens";;

let daw_RS = `memrange(d:int64,48) UNION memrange(wr:int64,32) UNION
              memrange(src:int64,24) UNION memrange(out:int64,m) UNION
              memrange(word_sub sp (word 400):int64,400) UNION
              memrange(q:int64,LENGTH(inp:byte list)) UNION
              memrange(word pc:int64,libsnappy_size) UNION
              memrange(word(pc + libsnappy_rw):int64,libsnappy_rw_size) UNION
              memrange(ea:int64,el)`;;
let daw_WS = `memrange(d:int64,48) UNION memrange(wr:int64,32) UNION
              memrange(src:int64,24) UNION memrange(out:int64,m) UNION
              memrange(word_sub sp (word 400):int64,400)`;;

let daw_W = `memrange(word_sub sp (word 112):int64,112) UNION
             memrange(word_sub sp (word 400):int64,288) UNION
             memrange(d:int64,41) UNION memrange(word_add d (word 41),5) UNION
             memrange(word_add src (word 8):int64,16) UNION
             memrange(word_add wr (word 8):int64,8) UNION memrange(out:int64,m)`;;

let daw_C = subst [daw_W,`w:int64->bool`]
 `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
  MAYCHANGE [SP; X18; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28;
             X29; X30] ,,
  MAYCHANGE [memory :> footprint w]`;;

let daw_common = subst [daw_RS,`rs:int64->bool`; daw_WS,`ws:int64->bool`]
 `aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
  read SP s = word_sub sp (word 112) /\
  read (memory :> bytes64 (word_sub sp (word 112))) s = x29 /\
  read (memory :> bytes64 (word_add (word_sub sp (word 112)) (word 8))) s =
    returnaddress /\
  read (memory :> bytes64 (word_add (word_sub sp (word 112)) (word 16))) s = x19 /\
  read (memory :> bytes64 (word_add (word_sub sp (word 112)) (word 24))) s = x20 /\
  read (memory :> bytes64 (word_add (word_sub sp (word 112)) (word 32))) s = x21 /\
  read (memory :> bytes64 (word_add (word_sub sp (word 112)) (word 40))) s = x22 /\
  read (memory :> bytes64 (word_add (word_sub sp (word 112)) (word 48))) s = x23 /\
  read (memory :> bytes64 (word_add (word_sub sp (word 112)) (word 56))) s = x24 /\
  read (memory :> bytes64 (word_add (word_sub sp (word 112)) (word 64))) s = x25 /\
  read (memory :> bytes64 (word_add (word_sub sp (word 112)) (word 72))) s = x26 /\
  read (memory :> bytes64 (word_add (word_sub sp (word 112)) (word 80))) s = x27 /\
  read (memory :> bytes64 (word_add (word_sub sp (word 112)) (word 88))) s = x28 /\
  read X19 s = word_add out (word(LENGTH (ob:byte list))) /\
  read X20 s = ipv /\
  read X22 s = d /\ read X25 s = wr /\
  read X23 s = word_add (word pc) (word 32256) /\
  read (memory :> bytes64 d) s = src /\
  read (memory :> bytes64 (word_add d (word 16))) s =
    word_add ipv (word(LENGTH (rest:byte list))) /\
  read (memory :> bytes8 (word_add d (word 40))) s = word 0 /\
  read (memory :> bytes64 src) s =
    word_add (word pc) (word vtable_ByteArraySource) /\
  read (memory :> bytes64 wr) s = out /\
  read (memory :> bytes64 (word_add wr (word 16))) s = word_add out (word m) /\
  read (memory :> bytes64 (word_add wr (word 24))) s =
    word_sub (word_add out (word m)) (word(MIN m 63)) /\
  read (memory :> bytelist(ipv,LENGTH rest)) s = rest /\
  read (memory :> bytelist(out,LENGTH ob)) s = ob /\
  read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s = rw /\
  read (memory :> bytes(ea,el)) s = ev /\
  (?e2. read events s = APPEND e2 e /\ memaccess_inset e2 rs ws) /\
  LENGTH ob <= m /\ ~(rest = []) /\ snappy_refill_ok rest /\
  snappy_decode_tags m inp [] = snappy_decode_tags m rest ob`;;

let daw_buf =
 `ipv = word_add q (word i) /\ i + LENGTH (rest:byte list) = LENGTH(inp:byte list) /\
  5 <= LENGTH rest /\
  read (memory :> bytes64 (word_add d (word 24))) s =
    word_add q (word(LENGTH inp - 4)) /\
  read (memory :> bytes64 (word_add d (word 32))) s = word(LENGTH inp) /\
  read (memory :> bytes64 (word_add src (word 8))) s = q /\
  read (memory :> bytes64 (word_add src (word 16))) s = word(LENGTH inp)`;;

let daw_scr =
 `ipv = word_add d (word 41) /\ i = 0 /\ LENGTH (rest:byte list) <= 4 /\
  read (memory :> bytes64 (word_add d (word 24))) s = word_add d (word 41) /\
  read (memory :> bytes64 (word_add d (word 32))) s = word 0 /\
  read (memory :> bytes64 (word_add src (word 8))) s =
    word_add q (word(LENGTH(inp:byte list))) /\
  read (memory :> bytes64 (word_add src (word 16))) s = word 0`;;

let daw_tag_extra =
  `read X26 s = word_zx(HD (rest:byte list)):int64 /\
   read X2 s = word_zx(HD rest):int64`;;

(* A cut point: PC offset, measure, extra facts, the state of the buffer.   *)
let daw_cut pcoff meas extra state =
  let tm = mk_conj(subst [mk_small_numeral pcoff,`k:num`]
                     `read PC s = word(pc + k):int64`,
                   mk_conj(daw_common, state)) in
  let tm = if extra = `T` then tm else mk_conj(tm,extra) in
  list_mk_exists([`ipv:int64`; `rest:byte list`; `ob:byte list`; `i:num`],
                 mk_conj(mk_eq(`n:num`,meas),tm));;

let daw_lb = daw_cut 0x63fc `2 * LENGTH(rest:byte list) + 1` `T` daw_buf;;
let daw_ls = daw_cut 0x63fc `2 * LENGTH(rest:byte list) + 1` `T` daw_scr;;
let daw_tb = daw_cut 0x6440 `2 * LENGTH(rest:byte list)` daw_tag_extra daw_buf;;
let daw_ts = daw_cut 0x6440 `2 * LENGTH(rest:byte list)` daw_tag_extra daw_scr;;

let daw_entry =
  mk_conj(`n = 2 * LENGTH(inp:byte list) + 2`,
          rhs(concl(BETA_CONV(mk_comb(daw_P,`s:armstate`)))));;

let daw_R =
  mk_abs(`n:num`,mk_abs(`s:armstate`,
    list_mk_disj [daw_entry; daw_lb; daw_ls; daw_tb; daw_ts]));;

(* The goal of one segment: from the disjunct pre to Q or a smaller cut.    *)
let daw_post = mk_abs(`s:armstate`,
  mk_disj(mk_comb(daw_Q,`s:armstate`),
          mk_exists(`m':num`,mk_conj(`m' < n`,
            list_mk_comb(daw_R,[`m':num`; `s:armstate`])))));;
let daw_post = (rand o concl o (DEPTH_CONV BETA_CONV)) daw_post;;

let daw_seg pre =
  mk_imp(daw_hyp,
    list_mk_icomb "ensures" [`arm`; mk_abs(`s:armstate`,pre); daw_post; daw_C]);;

let daw_exec = SNAPPY_DECOMPRESSOR_DECOMPRESS_ALL_TAGS_SNAPPY_ARRAY_WRITER_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* Lemmas for the code of DecompressAllTags<SnappyArrayWriter>.             *)
(* ------------------------------------------------------------------------- *)

let DAW_WORD_SUB_ADD_LEFT = prove
 (`!x y:int64. word_sub (word_add x y) x = y`, CONV_TAC WORD_RULE);;

let DAW_WORD_SUB_ADD_ADD = prove
 (`!x:int64 a b. word_sub (word_add x (word (a + b))) (word_add x (word a)) = word b`,
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

let DAW_WORD_SGT_FLAGS = prove
 (`!x y:int64.
     (~(val(word_sub x y) = 0) /\
      (ival(word_sub x y) < &0 <=> ~(ival x - ival y = ival(word_sub x y)))) <=>
     ival y < ival x`,
  BITBLAST_TAC);;

let DAW_IVAL_WORD_SMALL = prove
 (`!r. r < 2 EXP 63 ==> ival(word r:int64) = &r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INT_IVAL; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `r MOD 2 EXP 64 = r` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_LT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[]);;

(* ResetLimit: min<ptrdiff_t>(ip_limit_ - ip, 4) as the code computes it.   *)
let DAW_RESET_LIMIT = prove
 (`!r. r < 2 EXP 63
       ==> (if ~(~(val (word_sub (word r) (word 4):int64) = 0) /\
                 (ival (word_sub (word r) (word 4):int64) < &0 <=>
                  ~(ival (word r:int64) - &4 =
                    ival (word_sub (word r) (word 4):int64))))
            then word r else word 4:int64) = word(MIN r 4)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`word r:int64`; `word 4:int64`] DAW_WORD_SGT_FLAGS) THEN
  ASM_SIMP_TAC[DAW_IVAL_WORD_SMALL; ARITH_RULE `4 < 2 EXP 63`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INT_OF_NUM_LT] THEN
  COND_CASES_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let SNAPPY_REFILL_OK_5 = prove
 (`!rest:byte list. 5 <= LENGTH rest ==> snappy_refill_ok rest`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[snappy_refill_ok; GSYM LENGTH_EQ_NIL] THEN
  MP_TAC(SPEC `HD(rest:byte list)` SNAPPY_TAG_NEEDED_BOUNDS) THEN ASM_ARITH_TAC);;

let DAW_READ_BYTELIST_0 = prove
 (`!(a:int64) s. read (memory :> bytelist(a,0)) s = []`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; bytelist_clauses]);;

let DAW_WORD_ADD_EQ = prove
 (`!x:int64 a b. a < 2 EXP 64 /\ b < 2 EXP 64
                 ==> (word_add x (word a) = word_add x (word b) <=> a = b)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_RULE `word_add x a = word_add x b <=> a = b`] THEN
  REWRITE_TAC[WORD_EQ; DIMINDEX_64; CONG] THEN ASM_SIMP_TAC[MOD_LT]);;

(* The exit after the end of the stream (RefillTag found it empty).         *)
let DAW_EXIT_EMPTY = prove
 (`!out:int64 m (ob:byte list) s.
        LENGTH ob <= m /\ val out + m < 2 EXP 64 /\
        read (memory :> bytelist(out,LENGTH ob)) s = ob
        ==> ((T /\ word_add out (word(LENGTH ob)) = word_add out (word m)) <=>
             ~(snappy_decode_tags m [] ob = NONE)) /\
            (!x. snappy_decode_tags m [] ob = SOME x
                 ==> read (memory :> bytelist(out,m)) s = x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SNAPPY_DECODE_TAGS_NIL] THEN
  SUBGOAL_THEN `word_add (out:int64) (word(LENGTH(ob:byte list))) = word_add out (word m) <=>
                LENGTH ob = m` SUBST1_TAC THENL
   [MATCH_MP_TAC DAW_WORD_ADD_EQ THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT];
    GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_MESON_TAC[]]);;

(* scratch_ is not split by the top of the address space.                  *)
let DAW_SCRATCH_NOWRAP = prove
 (`!d:int64. aligned 8 d ==> val(word_add d (word 41)) + 5 < 2 EXP 64`,
  GEN_TAC THEN REWRITE_TAC[aligned; DIVIDES_MOD] THEN DISCH_TAC THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `d:int64` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  ASM_CASES_TAC `val(d:int64) + 41 < 18446744073709551616` THENL
   [ASM_SIMP_TAC[MOD_LT] THEN
    MP_TAC(SPECL [`val(d:int64)`; `8`] DIVISION) THEN
    ASM_REWRITE_TAC[ARITH_EQ; ADD_CLAUSES] THEN DISCH_TAC THEN
    SUBGOAL_THEN `8 * val(d:int64) DIV 8 < 8 * 2305843009213693947`
      MP_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[LT_MULT_LCANCEL]] THEN
    ASM_ARITH_TAC;
    SUBGOAL_THEN `(val(d:int64) + 41) MOD 18446744073709551616 =
                  (val d + 41) - 18446744073709551616` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC]]);;

(* A part of a region at an offset.                                         *)
let DAW_NONOVERLAPPING_SUB = prove
 (`!(a:int64) n i r b k.
        nonoverlapping (a,n) (b,k) /\ i + r <= n
        ==> nonoverlapping (word_add a (word i),r) (b,k)`,
  REWRITE_TAC[NONOVERLAPPING_MEMRANGE] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `i:num`; `r:num`; `n:num`] MEMRANGE_OFFSET_SUBSET) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]]);;

let DAW_MEMRANGE_SUB = prove
 (`!(a:int64) n i r. i + r <= n
        ==> memrange(word_add a (word i),r) SUBSET memrange(a,n)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEMRANGE_OFFSET_SUBSET THEN ASM_ARITH_TAC);;

(* The bytes after a prefix h of l.                                         *)
let DAW_BYTELIST_SUFFIX = prove
 (`!(m:(S,N word->byte)component) a (l:byte list) h l' s.
        read (m :> bytelist(a,LENGTH l)) s = l /\ l = APPEND h l'
        ==> read (m :> bytelist(word_add a (word(LENGTH l - LENGTH l')),
                                LENGTH l')) s = l'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH(l:byte list) - LENGTH(l':byte list) = LENGTH(h:byte list)`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `read ((m:(S,N word->byte)component) :> bytelist(a,LENGTH(l:byte list))) (s:S) = l` THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; READ_BYTELIST_SPLIT] THEN
  DISCH_THEN(fun th ->
    let x = rand(rator(lhs(concl th))) and y = rand(lhs(concl th)) in
    let hh = rand(rator(rhs(concl th))) and ll = rand(rhs(concl th)) in
    let lth = ISPECL [x; y; hh; ll] SNAPPY_APPEND_EQ_PREFIX in
    let eq = MP lth (CONJ (REWRITE_CONV[LENGTH_READ_BYTELIST]
                             (mk_eq(mk_comb(`LENGTH:byte list->num`,x),
                                    mk_comb(`LENGTH:byte list->num`,hh))) |>
                           EQT_ELIM) th) in
    MP_TAC th THEN REWRITE_TAC[eq; APPEND_LCANCEL]));;

let DAW_SLOP = prove
 (`!out:int64 m. m < 2 EXP 64
     ==> word_sub (word_sub (word_add out (word m)) (word(MIN m 63))) out =
         word(m - MIN 63 m)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `MIN m 63 = MIN 63 m /\ MIN 63 m <= m` STRIP_ASSUME_TAC THENL
   [ARITH_TAC; ASM_SIMP_TAC[WORD_SUB]] THEN CONV_TAC WORD_RULE);;

let DAW_VAL_OFFSET = prove
 (`!(q:int64) n i r. val q + n < 2 EXP 64 /\ i + r <= n
                     ==> val(word_add q (word i)) + r < 2 EXP 64`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `i MOD 2 EXP 64 = i` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(val(q:int64) + i) MOD 2 EXP 64 = val q + i` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let DAW_WORD_ADD_SUB_ADD = prove
 (`!(x:int64) a b. b <= a
        ==> word_add (word_add x (word (a - b))) (word b) = word_add x (word a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let DAW_REFILL_OK_NONNIL = prove
 (`!rest:byte list. snappy_refill_ok rest ==> ~(rest = [])`,
  SIMP_TAC[snappy_refill_ok]);;

let DAW_WORD_ADD_SUB_CANCEL = prove
 (`!(x:int64) a b. word_sub (word_add x (word (a + b))) (word b) = word_add x (word a)`,
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

let DAW_READ_HD = prove
 (`!(a:int64) l s. read (memory :> bytelist(a,LENGTH l)) s = l /\ ~(l = [])
                   ==> read (memory :> bytes8 a) s = HD l`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `l:byte list`; `0`; `s:armstate`] READ_MEMORY_BYTELIST_EL) THEN
  ASM_REWRITE_TAC[WORD_ADD_0; EL; LENGTH_EQ_NIL; ARITH_RULE `0 < n <=> ~(n = 0)`]);;

let DAW_BYTES32_LOW = prove
 (`!(a:int64) (l:byte list) k s.
        read (memory :> bytelist(a,LENGTH l)) s = l /\ k <= 4 /\ k <= LENGTH l
        ==> val(read (memory :> bytes32 a) s) MOD 2 EXP (8 * k) =
            num_of_bytelist(SUB_LIST(0,k) l)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[BYTES32_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[READ_BYTES_MOD] THEN
  ASM_SIMP_TAC[ARITH_RULE `k <= 4 ==> MIN 4 k = k`] THEN
  MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`; `a:int64`; `0`; `k:num`;
                 `LENGTH(l:byte list)`; `s:armstate`] READ_BYTELIST_SUB_LIST) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; WORD_ADD_0] THEN
  REWRITE_TAC[READ_BYTELIST_EQ_BYTES; READ_COMPONENT_COMPOSE] THEN
  SIMP_TAC[]);;

let DAW_WORD_ADD_SUB_NUM = prove
 (`!(x:int64) a b. b <= a
        ==> word_sub (word_add x (word a)) (word b) = word_add x (word(a - b))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WORD_SUB] THEN CONV_TAC WORD_RULE);;

let DAW_NONOVERLAPPING_ADJ = prove
 (`!(a:int64) n k. val a + n + k <= 2 EXP 64
                   ==> nonoverlapping (a,n) (word_add a (word n),k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NONOVERLAPPING_MEMRANGE] THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_MEMRANGE; NOT_IN_EMPTY] THEN
  X_GEN_TAC `z:int64` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:num` STRIP_ASSUME_TAC)
                              (X_CHOOSE_THEN `y:num` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `z = word_add (a:int64) (word x)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
              WORD_RULE `word_add a x = word_add a y <=> x = y`] THEN
  REWRITE_TAC[WORD_EQ; DIMINDEX_64; CONG] THEN
  SUBGOAL_THEN `(n + y) MOD 2 EXP 64 = n + y /\ x MOD 2 EXP 64 = x`
    (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(ISPEC `a:int64` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_64] THEN
    ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let DAW_WORD_AND_MASK32 = prove
 (`!(b:int32) k n. val b MOD 2 EXP (8 * k) = n /\ k <= 4
        ==> word_and b (word(2 EXP (8 * k) - 1)) = word n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_AND_MASK_WORD] THEN
  ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  TRANS_TAC LTE_TRANS `2 EXP (8 * k)` THEN
  ASM_REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ; LE_EXP] THEN ASM_ARITH_TAC);;

let DAW_NONOVERLAPPING_SUB_R = prove
 (`!(a:int64) n i r b k.
        nonoverlapping (b,k) (a,n) /\ i + r <= n
        ==> nonoverlapping (b,k) (word_add a (word i),r)`,
  MESON_TAC[DAW_NONOVERLAPPING_SUB; NONOVERLAPPING_SYM]);;

(* The fast copy of AppendFromSelf: memmove of 64 bytes from op - off.     *)
let DAW_COPY_SRC = prove
 (`!(out:int64) (ob:byte list) off len x s.
        read (memory :> bytelist(out,LENGTH ob)) s = ob /\
        read (memory :> bytes(word_add out (word(LENGTH ob - off)),64)) s = x /\
        len <= off /\ off <= LENGTH ob /\ len <= 64
        ==> x MOD 2 EXP (8 * len) =
            num_of_bytelist(SUB_LIST(LENGTH ob - off,len) ob)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && is_var(rhs(concl th)))) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_MOD] THEN
  ASM_SIMP_TAC[ARITH_RULE `len <= 64 ==> MIN 64 len = len`] THEN
  MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`; `out:int64`;
                 `LENGTH(ob:byte list) - off`; `len:num`; `LENGTH(ob:byte list)`;
                 `s:armstate`] READ_BYTELIST_SUB_LIST) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[READ_BYTELIST_EQ_BYTES; READ_COMPONENT_COMPOSE] THEN SIMP_TAC[]);;

let DAW_COPY_MEMMOVE = prove
 (`!(out:int64) (ob:byte list) off len x s.
        read (memory :> bytelist(out,LENGTH ob)) s = ob /\
        read (memory :> bytes(word_add out (word(LENGTH ob)),64)) s = x /\
        x MOD 2 EXP (8 * len) = num_of_bytelist(SUB_LIST(LENGTH ob - off,len) ob) /\
        len <= off /\ off <= LENGTH ob /\ len <= 64
        ==> read (memory :> bytelist(out,LENGTH(snappy_copy off len ob))) s =
            snappy_copy off len ob`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SNAPPY_COPY_NONOVERLAP; LENGTH_APPEND; LENGTH_SUB_LIST] THEN
  SUBGOAL_THEN `MIN len (LENGTH(ob:byte list) - (LENGTH ob - off)) = len`
    SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[READ_BYTELIST_SPLIT] THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  REWRITE_TAC[READ_BYTELIST_EQ_BYTES; LENGTH_SUB_LIST] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && is_binary "MOD" (lhs(concl th)))) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && is_var(rhs(concl th)))) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_MOD] THEN
  ASM_SIMP_TAC[ARITH_RULE `len <= 64 ==> MIN 64 len = len`]);;

let DAW_SUB_LIST_PREFIX_PREFIX = prove
 (`!(l:A list) k n. k <= n ==> SUB_LIST(0,k) (SUB_LIST(0,n) l) = SUB_LIST(0,k) l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[SUB_LIST_CLAUSES] THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `k:num` num_CASES) THEN
  STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
  REWRITE_TAC[SUB_LIST_CLAUSES; LE_SUC; ARITH_RULE `~(SUC k <= 0)`] THEN
  ASM_MESON_TAC[]);;

let DAW_WORD_SUB_ADD_LE = prove
 (`!(x:int64) a b. b <= a
        ==> word_sub (word_add x (word a)) (word_add x (word b)) = word(a - b)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WORD_SUB] THEN CONV_TAC WORD_RULE);;

(* The carry of a subtraction as the step tactics state it.                *)
let DAW_INT_SUB_LE = prove
 (`!a b:N word. &(val a) - &(val b):int = &(val(word_sub a b)) <=> val b <= val a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INT_VAL_WORD_SUB_CASES; INT_OF_NUM_LE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `b:N word` VAL_BOUND) THEN MP_TAC(ISPEC `a:N word` VAL_BOUND) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT; INT_OF_NUM_POW] THEN INT_ARITH_TAC);;

let DAW_INT_SUB_LE_NUM = prove
 (`!(a:N word) k. k < 2 EXP dimindex(:N)
        ==> (&(val a) - &k:int = &(val(word_sub a (word k))) <=> k <= val a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:N word`; `word k:N word`] DAW_INT_SUB_LE) THEN
  ASM_SIMP_TAC[VAL_WORD; MOD_LT]);;

(* The conversion for the integer form of a carry with a numeral.         *)
let DAW_INT_SUB_LE_NUM_CONV tm =
  match tm with
    Comb(Comb(Const("=",_),Comb(Comb(Const("int_sub",_),
         Comb(Const("int_of_num",_),Comb(Const("val",_),a))),
         Comb(Const("int_of_num",_),k))),_) when is_numeral k ->
      let th = ISPECL [a;k] DAW_INT_SUB_LE_NUM in
      let side = EQT_ELIM((DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
                          (lhand(concl th))) in
      let eq = MP th side in
      if lhs(concl eq) = tm then eq else failwith "DAW_INT_SUB_LE_NUM_CONV"
  | _ -> failwith "DAW_INT_SUB_LE_NUM_CONV";;

let DAW_SCRATCH_VAL = prove
 (`!d:int64 j. val(word_add d (word 41)) + 5 < 2 EXP 64 /\ j <= 5
        ==> val(word_add d (word (41 + j))) = val(word_add d (word 41)) + j`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_RULE `word_add (d:int64) (word (41 + j)) =
                         word_add (word_add d (word 41)) (word j)`] THEN
  MATCH_MP_TAC VAL_WORD_ADD_NOWRAP THEN ASM_ARITH_TAC);;

let DAW_BYTELIST_APPEND = prove
 (`!(m:(S,N word->byte)component) a (l1:byte list) l2 s.
        read (m :> bytelist(a,LENGTH l1)) s = l1 /\
        read (m :> bytelist(word_add a (word(LENGTH l1)),LENGTH l2)) s = l2
        ==> read (m :> bytelist(a,LENGTH(APPEND l1 l2))) s = APPEND l1 l2`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LENGTH_APPEND; READ_BYTELIST_SPLIT]);;

let DAW_LE_SIMPS = prove
 (`(!a b:num. ~(a <= b) \/ a = b <=> b <= a) /\
   (!a b:num. ~(a <= b) \/ b = a <=> b <= a) /\
   (!a b:num. a <= b /\ ~(a = b) <=> a < b) /\
   (!a b:num. a <= b /\ ~(b = a) <=> a < b)`,
  REPEAT CONJ_TAC THEN ARITH_TAC);;

let DAW_WORD_ZX_WORD = prove
 (`!n. n < 2 EXP dimindex(:M) /\ n < 2 EXP dimindex(:N)
       ==> word_zx (word n:M word):N word = word n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD] THEN
  ASM_SIMP_TAC[MOD_LT] THEN MATCH_MP_TAC MOD_LT THEN
  SUBGOAL_THEN `n MOD 2 EXP dimindex(:N) = n` (fun th -> REWRITE_TAC[th]) THEN
  ASM_SIMP_TAC[MOD_LT]);;

(* ------------------------------------------------------------------------- *)
(* The tag byte as the code takes it apart.                                 *)
(* ------------------------------------------------------------------------- *)

let DAW_TAG_AND3 = prove
 (`!c:byte. word_and (word_zx c:int32) (word 3) = word(val c MOD 4)`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; ARITH_RULE `3 = 2 EXP 2 - 1`] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32] THEN
  MP_TAC(ISPEC `c:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  DISCH_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `val(c:byte) MOD 4294967296 = val c` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(SPECL [`val(c:byte)`; `4`] DIVISION) THEN ARITH_TAC);;

(* The entries of the table kLengthMinusOffset (length_minus_offset_lib.ml) *)
(* for the copies with 1- and 2-byte offsets, as 16-bit numbers: the length *)
(* minus the bits 8..10 of the offset.                                      *)
let daw_lmo = new_definition
 `daw_lmo (c:byte) =
    if val c MOD 4 = 1
    then (val c DIV 4 MOD 8 + 4 + 65536 - 256 * (val c DIV 4 DIV 8)) MOD 65536
    else val c DIV 4 + 1`;;

let DAW_VAL_WORD_ZX_BYTE = prove
 (`!c:byte. val(word_zx c:int64) = val c`,
  GEN_TAC THEN MATCH_MP_TAC VAL_WORD_ZX THEN
  REWRITE_TAC[DIMINDEX_8; DIMINDEX_64] THEN ARITH_TAC);;

let DAW_LMO_IWORD = prove
 (`!c:byte. val c MOD 4 = 1 \/ val c MOD 4 = 2
            ==> iword(snappy_lmo c):int16 = word(daw_lmo c)`,
  GEN_TAC THEN REWRITE_TAC[snappy_lmo; daw_lmo] THEN
  MP_TAC(ISPEC `c:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SPEC_TAC(`val(c:byte)`,`v:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[]);;

let DAW_LMO_TABLE = prove
 (`!s pc c. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           (val c MOD 4 = 1 \/ val c MOD 4 = 2)
           ==> read (memory :> bytes16
                 (word_add (word pc) (word (32256 + 2 * val (word_zx c:int64))))) s =
               word(daw_lmo c)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  ASM_SIMP_TAC[SNAPPY_LMO_TABLE_ZX] THEN MATCH_MP_TAC DAW_LMO_IWORD THEN
  ASM_REWRITE_TAC[]);;

(* The length and the bits 8..10 of the offset as the code computes them.  *)
let DAW_LMO_CODE = prove
 (`!c:byte. val c MOD 4 = 1 \/ val c MOD 4 = 2
     ==> word_and (word_zx (word_sx (word(daw_lmo c):int16):int32):int64) (word 255) =
         word(if val c MOD 4 = 1 then val c DIV 4 MOD 8 + 4 else val c DIV 4 + 1) /\
         word_sub (word_zx (word(if val c MOD 4 = 1 then val c DIV 4 MOD 8 + 4
                                 else val c DIV 4 + 1):int64):int32)
                  (word_sx (word(daw_lmo c):int16)) =
         word(if val c MOD 4 = 1 then 256 * (val c DIV 4 DIV 8) else 0)`,
  GEN_TAC THEN REWRITE_TAC[daw_lmo] THEN
  MP_TAC(ISPEC `c:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SPEC_TAC(`val(c:byte)`,`v:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV);;

let DAW_ZX_ADD32 = prove
 (`!a b. a + b < 2 EXP 32
         ==> word_zx (word_add (word a) (word b):int32):int64 = word(a + b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD;
    GSYM WORD_ADD; DIMINDEX_32; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `x < 2 EXP 32 ==> x < 2 EXP 64`]);;

let DAW_NUM_OF_BYTELIST_SUB_BOUND = prove
 (`!(l:byte list) k. k <= LENGTH l
        ==> num_of_bytelist(SUB_LIST(0,k) l) < 2 EXP (8 * k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `SUB_LIST(0,k) (l:byte list)` NUM_OF_BYTELIST_BOUND) THEN
  ASM_SIMP_TAC[LENGTH_SUB_LIST; SUB_0; ARITH_RULE `k <= l ==> MIN k l = k`] THEN
  REWRITE_TAC[EXP_MULT] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let DAW_ZX_WORD32 = prove
 (`!n. n < 2 EXP 32 ==> word_zx (word n:int32):int64 = word n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD;
    DIMINDEX_32; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `x < 2 EXP 32 ==> x < 2 EXP 64`]);;

let DAW_TAG_AND3_64 = prove
 (`!c:byte. word_and (word_zx c:int64) (word 3) = word(val c MOD 4)`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; ARITH_RULE `3 = 2 EXP 2 - 1`] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; DAW_VAL_WORD_ZX_BYTE; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(SPECL [`val(c:byte)`; `4`] DIVISION) THEN ARITH_TAC);;

let DAW_TAG_BOUNDS = prove
 (`!c:byte. val c < 256 /\ val c DIV 4 < 64 /\ val c DIV 4 MOD 8 < 8 /\
            val c DIV 4 DIV 8 < 8`,
  GEN_TAC THEN MP_TAC(ISPEC `c:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `val(c:byte) DIV 4 < 64` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  CONJ_TAC THENL [MESON_TAC[MOD_LT_EQ; ARITH_RULE `~(8 = 0)`]; ALL_TAC] THEN
  ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC);;

let DAW_TAG_NEEDED = prove
 (`!rest:byte list.
     snappy_refill_ok rest
     ==> (val(HD rest) MOD 4 = 1 ==> 2 <= LENGTH rest) /\
         (val(HD rest) MOD 4 = 2 ==> 3 <= LENGTH rest) /\
         (val(HD rest) MOD 4 = 3 ==> 5 <= LENGTH rest) /\
         (val(HD rest) MOD 4 = 0 /\ ~(val(HD rest) DIV 4 < 60)
          ==> val(HD rest) DIV 4 - 58 <= LENGTH rest)`,
  GEN_TAC THEN REWRITE_TAC[snappy_refill_ok; snappy_tag_needed] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "<=" (concl th))) THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN
  TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(SPECL [`val(HD(rest:byte list))`; `4`] DIVISION) THEN ASM_ARITH_TAC);;

let DAW_TAG_USHR2 = prove
 (`!c:byte. word_ushr (word_zx c:int32) 2 = word(val c DIV 4)`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD_ZX_GEN; VAL_WORD;
                           DIMINDEX_32] THEN
  MP_TAC(ISPEC `c:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(c:byte) MOD 2 EXP 32 = val c` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  SUBGOAL_THEN `val(c:byte) DIV 4 <= val c` MP_TAC THENL
   [REWRITE_TAC[DIV_LE]; ASM_ARITH_TAC]);;

let DAW_WORD_ADD_ZX1 = prove
 (`!n. n + 1 < 2 EXP 32
       ==> word_zx (word_add (word n) (word 1):int32):int64 = word(n + 1)`,
  SIMP_TAC[DAW_ZX_ADD32]);;

let DAW_WORD_AND_255_SMALL = prove
 (`!n. n < 256 ==> word_and (word n:int64) (word 255) = word n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; ARITH_RULE `255 = 2 EXP 8 - 1`;
    VAL_WORD_AND_MASK_WORD; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `n MOD 2 EXP 64 = n` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let DAW_ZX_B32 = prove
 (`!(b:int32) n. val b MOD 2 EXP (8 * 4) = n ==> word_zx b:int64 = word n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD;
    DIMINDEX_32; DIMINDEX_64] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `b:int32` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `x < 4294967296 ==> x < 18446744073709551616`]);;

let DAW_ADD_ZX32_1 = prove
 (`!n. n < 2 EXP 32 ==> word_add (word_zx (word n:int32)) (word 1):int64 = word(n + 1)`,
  SIMP_TAC[DAW_ZX_WORD32; WORD_ADD]);;

let DAW_ZX64_WORD = prove
 (`!n. n < 2 EXP 32 ==> word_zx (word n:int64):int32 = word n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD;
    DIMINDEX_32; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `x < 2 EXP 32 ==> x < 2 EXP 64`]);;

let DAW_LONG_TAG = prove
 (`!c:byte. val c MOD 4 = 0 /\ ~(val c DIV 4 < 60)
            ==> val c = 240 \/ val c = 244 \/ val c = 248 \/ val c = 252`,
  GEN_TAC THEN MP_TAC(ISPEC `c:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SPEC_TAC(`val(c:byte)`,`v:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* One tag of the slow path in the decoding, by kind (rest = CONS c t).      *)
(* ------------------------------------------------------------------------- *)

let DAW_DECODE_STEP = prove
 (`!m (rest:byte list) ob.
        ~(rest = [])
        ==> snappy_decode_tags m rest ob =
            snappy_bind (snappy_tag_step m rest ob)
                        (\s. snappy_decode_tags m (FST s) (SND s))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [SNAPPY_DECODE_TAGS] THEN
  ASM_REWRITE_TAC[]);;

let DAW_TL_SUB_LIST = prove
 (`!t:A list. ~(t = []) ==> TL t = SUB_LIST(1,LENGTH t - 1) t`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; TL; LENGTH; SUC_SUB1] THEN
  REWRITE_TAC[ONE; SUB_LIST_CLAUSES; SUB_LIST_LENGTH]);;

let DAW_NUM_OF_BYTELIST_1 = prove
 (`!t:byte list. ~(t = []) ==> num_of_bytelist(SUB_LIST(0,1) t) = val(HD t)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; HD; ONE; SUB_LIST_CLAUSES] THEN
  REWRITE_TAC[num_of_bytelist] THEN ARITH_TAC);;

let DAW_DECODE_COPY1 = prove
 (`!m c (t:byte list) ob.
        val c MOD 4 = 1 /\ 1 <= LENGTH t
        ==> snappy_decode_tags m (CONS c t) ob =
            let off = 256 * (val c DIV 4 DIV 8) + num_of_bytelist(SUB_LIST(0,1) t)
            and len = val c DIV 4 MOD 8 + 4 in
            if 1 <= off /\ off <= LENGTH ob /\ LENGTH ob + len <= m
            then snappy_decode_tags m (SUB_LIST(1,LENGTH t - 1) t)
                                      (snappy_copy off len ob)
            else NONE`,
  REPEAT STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `~(t:byte list = [])` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[DAW_DECODE_STEP; NOT_CONS_NIL; SNAPPY_TAG_STEP_COPY1;
               DAW_NUM_OF_BYTELIST_1; GSYM DAW_TL_SUB_LIST] THEN
  REWRITE_TAC[snappy_copy_tag] THEN COND_CASES_TAC THEN REWRITE_TAC[snappy_bind]);;

let DAW_DECODE_COPY2 = prove
 (`!m c (t:byte list) ob.
        val c MOD 4 = 2 /\ 2 <= LENGTH t
        ==> snappy_decode_tags m (CONS c t) ob =
            let off = num_of_bytelist(SUB_LIST(0,2) t)
            and len = val c DIV 4 + 1 in
            if 1 <= off /\ off <= LENGTH ob /\ LENGTH ob + len <= m
            then snappy_decode_tags m (SUB_LIST(2,LENGTH t - 2) t)
                                      (snappy_copy off len ob)
            else NONE`,
  REPEAT STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_SIMP_TAC[DAW_DECODE_STEP; NOT_CONS_NIL; SNAPPY_TAG_STEP_COPY2] THEN
  REWRITE_TAC[snappy_copy_tag] THEN COND_CASES_TAC THEN REWRITE_TAC[snappy_bind]);;

let DAW_DECODE_COPY4 = prove
 (`!m c (t:byte list) ob.
        val c MOD 4 = 3 /\ 4 <= LENGTH t
        ==> snappy_decode_tags m (CONS c t) ob =
            let off = num_of_bytelist(SUB_LIST(0,4) t)
            and len = val c DIV 4 + 1 in
            if 1 <= off /\ off <= LENGTH ob /\ LENGTH ob + len <= m
            then snappy_decode_tags m (SUB_LIST(4,LENGTH t - 4) t)
                                      (snappy_copy off len ob)
            else NONE`,
  REPEAT STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_SIMP_TAC[DAW_DECODE_STEP; NOT_CONS_NIL; SNAPPY_TAG_STEP_COPY4] THEN
  REWRITE_TAC[snappy_copy_tag] THEN COND_CASES_TAC THEN REWRITE_TAC[snappy_bind]);;

let DAW_DECODE_LITERAL = prove
 (`!m c (t:byte list) ob.
        val c MOD 4 = 0 /\ val c DIV 4 < 60
        ==> snappy_decode_tags m (CONS c t) ob =
            let len = val c DIV 4 + 1 in
            if len <= LENGTH t /\ LENGTH ob + len <= m
            then snappy_decode_tags m (SUB_LIST(len,LENGTH t - len) t)
                                      (APPEND ob (SUB_LIST(0,len) t))
            else NONE`,
  REPEAT STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_SIMP_TAC[DAW_DECODE_STEP; NOT_CONS_NIL; SNAPPY_TAG_STEP_LITERAL] THEN
  REWRITE_TAC[snappy_literal] THEN COND_CASES_TAC THEN REWRITE_TAC[snappy_bind]);;

let DAW_DECODE_LONG_LITERAL = prove
 (`!m c (t:byte list) ob.
        val c MOD 4 = 0 /\ ~(val c DIV 4 < 60) /\ val c DIV 4 - 59 <= LENGTH t
        ==> snappy_decode_tags m (CONS c t) ob =
            let k = val c DIV 4 - 59 in
            let len = num_of_bytelist(SUB_LIST(0,k) t) + 1 in
            if k + len <= LENGTH t /\ LENGTH ob + len <= m
            then snappy_decode_tags m (SUB_LIST(k + len,LENGTH t - (k + len)) t)
                                      (APPEND ob (SUB_LIST(k,len) t))
            else NONE`,
  REPEAT STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_SIMP_TAC[DAW_DECODE_STEP; NOT_CONS_NIL; SNAPPY_TAG_STEP_LONG_LITERAL] THEN
  REWRITE_TAC[snappy_literal; SNAPPY_LENGTH_SUB_LIST_SUFFIX] THEN
  ABBREV_TAC `k = val(c:byte) DIV 4 - 59` THEN
  ABBREV_TAC `n = num_of_bytelist(SUB_LIST(0,k) (t:byte list)) + 1` THEN
  SUBGOAL_THEN `n <= LENGTH(t:byte list) - k <=> k + n <= LENGTH t` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[snappy_bind] THEN
  MATCH_MP_TAC(MESON[] `(a:byte list) = a' /\ (b:byte list) = b'
                        ==> snappy_decode_tags m a b = snappy_decode_tags m a' b'`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SNAPPY_SUFFIX_SUFFIX THEN ASM_ARITH_TAC;
    AP_TERM_TAC THEN MATCH_MP_TAC SNAPPY_SUFFIX_PREFIX THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Tactics.                                                                  *)
(* ------------------------------------------------------------------------- *)

let daw_debug = ref false;;

let daw_trunc n s = if String.length s > n then String.sub s 0 n ^ " ..." else s;;

let DAW_STATE_TAC (f:term -> tactic) : tactic = W(fun (asl,w) -> f (rand w));;

let daw_find_fact (p:term -> bool) asl = snd(find (fun (_,th) -> p(concl th)) asl);;

let DAW_START_TAC =
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; ALLPAIRS; ALL] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (fun th -> ASSUME_TAC th THEN
               LABEL_TAC "H_MEMCPY" (REWRITE_RULE[memcpy_correct_safe_contract] th))
    (CONJUNCTS_THEN2
      (fun th -> ASSUME_TAC th THEN
                 LABEL_TAC "H_MEMMOVE" (REWRITE_RULE[memmove_correct_safe_contract] th))
      STRIP_ASSUME_TAC));;

let DAW_INIT_TAC =
  ENSURES_INIT_TAC "s0" THEN
  ELF_RELOCATED_DATA_TAC ~defs:[snappy_libsnappy_gcc12_O2_relocated]
     ~select:(elf_slots_importing ["memmove"; "memcpy"]) THEN
  ELF_RELOCATED_DATA_TAC ~defs:[snappy_libsnappy_gcc12_O2_relocated]
     ~select:(elf_slots_at [0x1fc98; 0x1fca0]);;

let DAW_REFILL_EMPTY = SNAPPY_DECOMPRESSOR_REFILL_TAG_EMPTY_GCC12_O2_IMAGE_SUBROUTINE_SAFE;;
let DAW_REFILL_WINDOW = SNAPPY_DECOMPRESSOR_REFILL_TAG_WINDOW_GCC12_O2_IMAGE_SUBROUTINE_SAFE;;

(* A call of a contract th at the current state, its variables given by     *)
(* args (terms in the state s, evaluated by the facts), then rewritten with  *)
(* rws (the cases of its conditional results).                             *)
(* Registers without a fact in the current state get one, read r s = v for *)
(* a new variable v (the callee-saved registers that a contract gives back). *)
let DAW_GHOST_REGS_TAC (regs:term list) : tactic =
  W(fun (asl,w) ->
    let s = rand w in
    let has r = exists (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s1)),_) -> c = r && s1 = s
      | _ -> false) asl in
    let missing = filter (not o has) regs in
    MAP_EVERY (fun r ->
      let rd = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,r),s) in
      let v = genvar `:int64` in
      let eth = prove(mk_exists(v,mk_eq(rd,v)),EXISTS_TAC rd THEN REFL_TAC) in
      X_CHOOSE_THEN (mk_var("g_"^fst(dest_const r)^"_"^string_of_int(length asl),`:int64`))
        ASSUME_TAC eth) missing);;

let DAW_CALL_TAC ?(subs=[]) (th:thm) (args:term list) (rws:thm list) sname : tactic =
  W(fun (asl,w) ->
    let s = rand w in
    let ev t = arm_bstep_eval asl s (vsubst [s,`s:armstate`] t) in
    let sth = SPECL (map ev args) th in
    let sth = CONV_RULE(REWRITE_CONV(WORD_ADD_0 :: SUB_0 :: rws)) sth in
    ARM_BSTEP_CONTRACT_SUB_TAC subs daw_exec sth [] sname);;

let DAW_CALL_GHOST_TAC ?(subs=[]) (th:thm) (args:term list) (rws:thm list) sname : tactic =
  DAW_GHOST_REGS_TAC [`X19`;`X20`;`X21`;`X22`;`X23`;`X24`;`X25`;`X26`;`X27`;`X28`;`X29`] THEN
  DAW_CALL_TAC ~subs th args rws sname;;

let daw_refill_args p n k ip rest =
  [`read events s`; `d:int64`; `src:int64`; p; n; k; ip; rest; `pc:num`; `rw:num`;
   `read SP s`; `read X30 s`; `read X19 s`; `read X20 s`; `read X21 s`;
   `read X22 s`; `read X23 s`; `read X24 s`; `read X29 s`;
   `ea:int64`; `el:num`; `ev:num`];;

(* Choose the k-th (from 1) of n disjuncts.                                  *)
let rec DISJ_SELECT_TAC k n =
  if n = 1 then ALL_TAC
  else if k = 1 then DISJ1_TAC
  else DISJ2_TAC THEN DISJ_SELECT_TAC (k - 1) (n - 1);;

(* Arithmetic from the arithmetic facts among the assumptions (no states,   *)
(* no disequalities, which make ARITH_TAC split cases).                     *)
let rec daw_arith_fact t =
  match t with
    Comb(Const("~",_),a) -> daw_arith_fact a
  | Comb(Comb(Const(("/\\"|"\\/"|"==>"),_),a),b) -> daw_arith_fact a && daw_arith_fact b
  | Comb(Comb(Const(("<"|"<="),_),a),_) -> type_of a = `:num`
  | Comb(Comb(Const("=",_),a),_) -> type_of a = `:num`
  | Const(("F"|"T"),_) -> true
  | _ -> false;;

let DAW_ARITH_TAC : tactic = fun (asl,w) ->
  let ok th = let c = concl th in
    daw_arith_fact c &&
    not(is_neg c && is_eq(dest_neg c)) &&
    not(exists (fun v -> type_of v = `:armstate`) (frees c)) in
  if not(daw_arith_fact w) then failwith "DAW_ARITH_TAC: not arithmetic" else
  let ths = filter ok (map snd asl) in
  let rec has_disj t = match t with
      Comb(Comb(Const(("\\/"|"==>"),_),_),_) -> true
    | Comb(Const("~",_),a) -> has_disj a
    | Comb(Comb(Const("/\\",_),a),b) -> has_disj a || has_disj b
    | _ -> false in
  let atomic = filter (fun th -> not(has_disj(concl th))) ths in
  let fv = frees w in
  let rec take n l = if n = 0 then [] else match l with h::t -> h::take (n-1) t | [] -> [] in
  let disj = take 8 (filter (fun th -> has_disj(concl th)) ths) in
  let _ = fv in
  let near = atomic @ disj in
  let ths = near in
  let tac ths = MAP_EVERY MP_TAC ths THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC in
  let attempt ths g = try tac ths g with Stack_overflow -> failwith "DAW_ARITH_TAC: stack" in
  (attempt atomic ORELSE
   (fun g -> if List.length near = List.length atomic then failwith "" else attempt near g) ORELSE
   (fun g -> if List.length ths = List.length near then failwith "" else attempt ths g) ORELSE
   (fun g -> if !daw_debug then
       (Printf.printf "DAW_ARITH_FAIL %s\n" (string_of_term w);
        List.iter (fun th -> Printf.printf "   | %s\n" (daw_trunc 500 (string_of_term(concl th))))
          (filter ok (map snd asl)); Format.print_flush());
     failwith ("DAW_ARITH_TAC: `" ^ daw_trunc 400 (string_of_term w) ^ "`")))
  (asl,w);;

let daw_offset_from (b:term) (a:term) =
  let rec go a = if a = b then `0` else
    match a with
      Comb(Comb(Const("word_add",_),x),Comb(Const("word",_),t)) ->
        let u = go x in if u = `0` then t else mk_binop `(+):num->num->num` u t
    | Comb(Const("word",_) as wd,Comb(Comb(Const("+",_),x),t))
        when mk_comb(wd,x) = b -> t
    | _ -> failwith "daw_offset_from" in
  go a;;

(* Addresses as word_add base (word t).                                     *)
let DAW_ADDR_CONV = REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THENC NUM_REDUCE_CONV;;

(* The regions of the events (and of the callees' memaccess_inset facts)   *)
(* that are not within the sets rs by footprint_subset_rule get a SUBSET     *)
(* fact into the input, the output or the decompressor, by their offset     *)
(* from the base (DAW_MEMRANGE_SUB, the bound by arithmetic).                *)

(* |- a = b for two addresses: equal canonical forms, or the same base and  *)
(* offsets equal by arithmetic.                                             *)
let daw_addr_eq asl a b =
  if a = b then REFL a else
  let ea = DAW_ADDR_CONV a and eb = DAW_ADDR_CONV b in
  let ca = rhs(concl ea) and cb = rhs(concl eb) in
  if ca = cb then TRANS ea (SYM eb) else
  match ca,cb with
    Comb(Comb(Const("word_add",_) as f,x),Comb(Const("word",_) as wd,t1)),
    Comb(Comb(Const("word_add",_),y),Comb(Const("word",_),t2)) when x = y ->
      let th = TAC_PROOF((asl,mk_eq(t1,t2)),DAW_ARITH_TAC) in
      TRANS ea (TRANS (AP_TERM (mk_comb(f,x)) (AP_TERM wd th)) (SYM eb))
  | _ -> failwith "daw_addr_eq";;

(* A fact read (memory :> bytelist(a,LENGTH r)) s = r at the address a,    *)
(* from one at an equal address.                                            *)
let daw_bytelist_at asl s a =
  tryfind (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
           Comb(Comb(Const(":>",_),Const("memory",_)),
                Comb(Const("bytelist",_),Comb(Comb(Const(",",_),b),
                     Comb(Const("LENGTH",_),r))))),s1)),r')
        when s1 = s && r = r' ->
        let eq = daw_addr_eq asl b a in
        if b = a then th else SUBS[eq] th
    | _ -> fail()) asl;;

(* word_zx (word n) = word n when n fits both sizes (arithmetic).          *)
let DAW_ZX_CONV asl tm =
  match tm with
    Comb(Const("word_zx",ty),(Comb(Const("word",_),n) as wn)) ->
      let m = hd(snd(dest_type(type_of wn))) and nn = hd(snd(dest_type(type_of tm))) in
      let th = INST_TYPE [m,`:M`; nn,`:N`] DAW_WORD_ZX_WORD in
      let th = SPEC n th in
      let hyp = (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) (lhand(concl th)) in
      let hth = EQ_MP (SYM hyp) (TAC_PROOF((asl,rhs(concl hyp)),CONJ_TAC THEN DAW_ARITH_TAC)) in
      MP th hth
  | _ -> failwith "DAW_ZX_CONV";;

let daw_bases = [`q:int64`,`LENGTH(inp:byte list)`; `out:int64`,`m:num`; `d:int64`,`48`;
                 `word pc:int64`,`libsnappy_size:num`];;

let DAW_REGION_FACTS_TAC (arith:tactic) (sets:term list) : tactic =
  fun (asl,w) ->
    set_component_assumptions (map snd asl);
    let v,bod = dest_exists w in
    let t = lhand(lhand bod) in
    let evth = daw_find_fact (fun c -> is_eq c && lhs c = t) asl in
    let rec regions tm =
      match tm with
        Comb(Comb(Const("CONS",_),e),r) ->
          (match e with
             Comb(Const(("EventLoad"|"EventStore"),_),p) -> dest_pair p :: regions r
           | _ -> regions r)
      | Comb(Comb(Const("APPEND",_),l),r) ->
          let sub = try
              let th = daw_find_fact (fun c -> match c with
                  Comb(Comb(Comb(Const("memaccess_inset",_),l'),_),_) -> l' = l
                | _ -> false) asl in
              let rec un st = match st with
                  Comb(Comb(Const("UNION",_),a),b) -> un a @ un b
                | Comb(Const("memrange",_),p) -> [dest_pair p]
                | _ -> [] in
              un (rand(rator(concl th))) @ un (rand(concl th))
            with Failure _ -> [] in
          sub @ regions r
      | _ -> [] in
    let rs = setify(regions (rhs(concl evth))) in
    let need (a,k) =
      let r = mk_icomb(`memrange:int64#num->int64->bool`,mk_pair(a,k)) in
      not(exists (fun st -> can (footprint_subset_rule r) st) sets) in
    let fact (a,k) =
      let eq = (TOP_DEPTH_CONV (DAW_ZX_CONV asl) THENC DAW_ADDR_CONV) a in
      let a' = rhs(concl eq) in
      tryfind (fun (b,n) ->
        let t = daw_offset_from b a' in
        let le = mk_binary "<=" (mk_binop `(+):num->num->num` t k,n) in
        let lth = TAC_PROOF((asl,le),arith) in
        let th = MP (ISPECL [b;n;t;k] DAW_MEMRANGE_SUB) lth in
        let ad = lhand(rand(lhand(concl th))) in
        let eq2 = TRANS eq (SYM(DAW_ADDR_CONV ad)) in
        CONV_RULE(LAND_CONV(RAND_CONV(LAND_CONV(K(SYM eq2))))) th) daw_bases in
    let facts = mapfilter (fun r -> if need r then
        (try fact r with Failure msg ->
          (if !daw_debug then Printf.printf "DAW_REGION_FACTS: no fact for %s: %s\n%!"
             (string_of_term (mk_pair r)) msg); fail())
      else fail()) rs in
    MAP_EVERY ASSUME_TAC facts (asl,w);;

(* The events of the current state, as regions of loads and stores, for   *)
(* the message of a failure.                                                *)
let daw_event_regions asl t =
  let evth = daw_find_fact (fun c -> is_eq c && lhs c = t) asl in
  let rec go tm = match tm with
      Comb(Comb(Const("CONS",_),e),r) ->
        (match e with
           Comb(Const(("EventLoad"|"EventStore") as k,_),p) -> (k,dest_pair p) :: go r
         | _ -> go r)
    | Comb(Comb(Const("APPEND",_),l),r) -> ("list",(l,`0`)) :: go r
    | _ -> [] in
  go (rhs(concl evth));;

let DAW_EVENTS_TAC : tactic =
  W(fun (asl,w) ->
    let v,bod = dest_exists w in
    let rs = rand(rator(rand bod)) and ws = rand(rand bod) in
    DAW_REGION_FACTS_TAC DAW_ARITH_TAC [rs] THEN
    W(fun (asl,w) ->
      let t = lhand(lhand(snd(dest_exists w))) in
      let evth = snd(find (fun (_,th) -> is_eq(concl th) && lhand(concl th) = t) asl) in
      REWRITE_TAC[evth] THEN
      (fun g -> try MEMACCESS_INSET_TAC g with Failure _ ->
         set_component_assumptions (map snd asl);
         let bad = mapfilter (fun (k,(a,n)) ->
             if k = "list" then fail() else
             let r = mk_icomb(`memrange:int64#num->int64->bool`,mk_pair(a,n)) in
             if can (footprint_subset_rule r) (if k = "EventLoad" then rs else ws)
             then fail() else string_of_term r) (daw_event_regions asl t) in
         failwith ("DAW_EVENTS_TAC: regions not in the sets: " ^
                   daw_trunc 1500 (String.concat "; " bad)))));;



(* read c s = t from an assumption read c s = t0, both addresses canonical *)
(* and the offsets equal by arithmetic.                                     *)
let DAW_WORD_EQ_TAC : tactic = fun (asl,w) ->
  let l,r = dest_eq w in
  let th0 = daw_find_fact (fun c -> is_eq c && lhs c = l) asl in
  let t0 = rhs(concl th0) in
  let e1 = DAW_ADDR_CONV t0 and e2 = DAW_ADDR_CONV r in
  (GEN_REWRITE_TAC LAND_CONV [th0] THEN
   GEN_REWRITE_TAC LAND_CONV [e1] THEN GEN_REWRITE_TAC RAND_CONV [e2] THEN
   AP_TERM_TAC THEN AP_TERM_TAC THEN DAW_ARITH_TAC) (asl,w);;

let DAW_CONJ_TAC (extra:thm list) : tactic =
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         ASM_REWRITE_TAC extra THEN NO_TAC;
         ASM_REWRITE_TAC extra THEN CONV_TAC WORD_RULE THEN NO_TAC;
         ASM_SIMP_TAC (DAW_WORD_ADD_SUB_ADD :: extra) THEN NO_TAC;
         DAW_WORD_EQ_TAC;
         DAW_ARITH_TAC;
         (MATCH_MP_TAC DAW_REFILL_OK_NONNIL THEN FIRST_ASSUM ACCEPT_TAC);
         (REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN DAW_ARITH_TAC);
         (MATCH_MP_TAC SNAPPY_REFILL_OK_5 THEN DAW_ARITH_TAC);
         DAW_EVENTS_TAC];;

(* The leaf at a cut point: disjunct k of R (1 entry, 2 L buffer, 3 L      *)
(* scratch, 4 T buffer, 5 T scratch), the measure meas and the witnesses.   *)
let DAW_CUT_LEAF_TAC k meas (wits:term list) (mtac:tactic) (extra:thm list) : tactic =
  BSTEP_FINAL_TAC THEN DISJ2_TAC THEN EXISTS_TAC meas THEN
  CONJ_TAC THENL [mtac; ALL_TAC] THEN
  DISJ_SELECT_TAC k 5 THEN MAP_EVERY EXISTS_TAC wits THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  (fun (asl,w) -> try DAW_CONJ_TAC extra (asl,w) with Failure _ ->
     if is_exists w && name_of(fst(dest_exists w)) = "e2" then DAW_EVENTS_TAC (asl,w) else
     failwith ("DAW_CUT_LEAF_TAC: unsolved `" ^ daw_trunc 600 (string_of_term w) ^ "`"));;

(* The exit (ret) with eof_ = bitval ok; dth: snappy_decode_tags m inp [] = *)
(* NONE (ok = F) or = snappy_decode_tags m [] ob (ok = T, the end).          *)
let DAW_EXIT_TAC (ok:term) (dth:thm) : tactic =
  let empty_th (asl,w) =
    let s = rand w in
    let ob = rand(rhs(concl dth)) in
    let th = daw_find_fact (fun c -> c = subst [ob,`ob:byte list`; s,`s:armstate`]
               `read (memory :> bytelist(out,LENGTH(ob:byte list))) s = ob`) asl in
    let lth = daw_find_fact (fun c -> c = subst [ob,`ob:byte list`]
               `LENGTH(ob:byte list) <= m`) asl in
    let nw = MP (ARITH_RULE `val(out:int64) + m + 64 < 2 EXP 64 ==> val out + m < 2 EXP 64`)
                (ASSUME `val(out:int64) + m + 64 < 2 EXP 64`) in
    MATCH_MP DAW_EXIT_EMPTY (CONJ lth (CONJ nw th)) in
  fun (asl,w) ->
   let lth = if ok = `F` then TRUTH else empty_th (asl,w) in
   let opfix (asl,w) =
     (* the op_ value as word_add out (word (LENGTH ob)) *)
     try
       let ob = rand(rhs(concl dth)) in
       let t = find_term (fun t -> match t with
           Comb(Comb(Const("=",_),a),b) -> b = `word_add out (word m):int64` && a <> b
         | _ -> false) w in
       let a = lhand t in
       let target = mk_binop `word_add:int64->int64->int64` `out:int64`
                      (mk_comb(`word:num->int64`,mk_comb(`LENGTH:byte list->num`,ob))) in
       if a = target then ALL_TAC (asl,w) else
       let eq = daw_addr_eq asl a target in
       REWRITE_TAC[eq] (asl,w)
     with Failure _ -> ALL_TAC (asl,w) in
   let okpart =
     EXISTS_TAC ok THEN
     (if ok = `F` then ASM_REWRITE_TAC[BITVAL_CLAUSES]
      else
        ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN opfix THEN
        REWRITE_TAC[WORD_RULE `(out:int64) = word_add out (word m) <=>
                                 word_add out (word 0) = word_add out (word m)`] THEN
        REWRITE_TAC[REWRITE_RULE[] (CONJUNCT1 lth);
                    REWRITE_RULE[LENGTH] (CONJUNCT1 lth)])
   and allpart =
     (if ok = `F` then REWRITE_TAC[option_DISTINCT]
      else ACCEPT_TAC(CONJUNCT2 lth)) in
   let rest_tac (asl,w) =
     if is_exists w && name_of(fst(dest_exists w)) = "ok" then okpart (asl,w)
     else if is_forall w then allpart (asl,w)
     else if is_exists w && name_of(fst(dest_exists w)) = "e2" then DAW_EVENTS_TAC (asl,w)
     else failwith ("DAW_EXIT_TAC: unsolved `" ^ daw_trunc 600 (string_of_term w) ^ "`") in
   (BSTEP_FINAL_TAC THEN DISJ1_TAC THEN REWRITE_TAC[dth] THEN
    REPEAT CONJ_TAC THEN TRY(DAW_CONJ_TAC [WORD_ADD_0]) THEN rest_tac) (asl,w);;

let DAW_NIL_OUT_TAC =
  DAW_STATE_TAC (fun s -> ASSUME_TAC(REWRITE_RULE[GSYM(INST_TYPE [`:byte`,`:A`] (CONJUNCT1 LENGTH))]
     (SPECL [`out:int64`; s] DAW_READ_BYTELIST_0))) THEN
  ASSUME_TAC(prove(`LENGTH([]:byte list) <= m`, REWRITE_TAC[LENGTH; LE_0]));;

(* ------------------------------------------------------------------------- *)
(* Running the code: one step at a time, branches on data split and the     *)
(* impossible cases closed by arithmetic (DAW_KILL_TAC), calls by PC, and    *)
(* the leaf at the return or at a cut point (after at least one step).       *)
(* ------------------------------------------------------------------------- *)

let daw_arith_ok th =
  let c = concl th in
  daw_arith_fact c &&
  not(is_neg c && is_eq(dest_neg c)) &&
  not(exists (fun v -> type_of v = `:armstate`) (frees c));;

(* val of an address in scratch_ (d + 41 .. d + 46, which do not wrap).     *)
let DAW_SCRATCH_VAL_CONV asl tm =
  match tm with
    Comb(Const("val",_),a) when type_of a = `:int64` ->
      let ea = DAW_ADDR_CONV a in
      (match rhs(concl ea) with
         Comb(Comb(Const("word_add",_),dd),Comb(Const("word",_),t))
           when dd = `d:int64` && t <> `41` ->
           let j = mk_binop `(-):num->num->num` t `41` in
           let le = TAC_PROOF((asl,mk_conj(mk_binary "<=" (`41`,t),mk_binary "<=" (j,`5`))),
                      CONJ_TAC THEN DAW_ARITH_TAC) in
           let nw = daw_find_fact (fun c -> c = `val(word_add d (word 41):int64) + 5 < 2 EXP 64`) asl in
           let th = MP (SPECL [`d:int64`; j] DAW_SCRATCH_VAL) (CONJ nw (CONJUNCT2 le)) in
           let eq = AP_TERM `word:num->int64` (MP (ARITH_RULE(mk_imp(concl(CONJUNCT1 le),
                      mk_eq(mk_binop `(+):num->num->num` `41` j,t)))) (CONJUNCT1 le)) in
           let th = CONV_RULE(LAND_CONV(RAND_CONV(RAND_CONV(K eq)))) th in
           TRANS (AP_TERM (rator tm) ea) th
       | _ -> failwith "DAW_SCRATCH_VAL_CONV")
  | _ -> failwith "DAW_SCRATCH_VAL_CONV";;

let daw_norm_cond_conv (rest:(string*thm) list) : conv =
  let rec has_disj t = match t with
      Comb(Comb(Const(("\\/"|"==>"),_),_),_) -> true
    | Comb(Const("~",_),a) -> has_disj a
    | Comb(Comb(Const("/\\",_),a),b) -> has_disj a || has_disj b
    | _ -> false in
  let ths = filter (fun th -> daw_arith_ok th && not(has_disj(concl th))) (map snd rest) in
  (REWRITE_CONV[VAL_WORD_SUB_EQ_0; DAW_INT_SUB_LE; COND_EXPAND;
                                          DE_MORGAN_THM; NOT_CLAUSES] THENC
                             DEPTH_CONV DAW_INT_SUB_LE_NUM_CONV THENC
                             DEPTH_CONV (fun t -> match t with
                                 Comb(Const("val",_),Comb(Const("word",_),k))
                                   when type_of(rand t) = `:int32` ->
                                   let th = ISPEC k (INST_TYPE [`:32`,`:N`] VAL_WORD_EQ) in
                                   let th = REWRITE_RULE[DIMINDEX_32] th in
                                   MP th (TAC_PROOF((map (fun th -> ("",th)) ths,lhand(concl th)),
                                          MAP_EVERY MP_TAC ths THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC))
                               | _ -> failwith "") THENC
                             DEPTH_CONV (DAW_SCRATCH_VAL_CONV rest) THENC
                             TOP_DEPTH_CONV (VAL_NOWRAP_CONV ths) THENC
                             NUM_REDUCE_CONV THENC
                             REWRITE_CONV[DAW_LE_SIMPS; NOT_LE; NOT_LT]);;

let DAW_NORM_COND_TAC : tactic = fun (asl,w) ->
  match asl with
    [] -> ALL_TAC (asl,w)
  | (_,cth)::rest ->
      try
        let th' = CONV_RULE (daw_norm_cond_conv rest) cth in
        if concl th' = concl cth then ALL_TAC (asl,w) else ASSUME_TAC th' (asl,w)
      with Failure _ -> ALL_TAC (asl,w);;

let DAW_KILL_TAC : tactic =
  fun (asl,w) ->
    match asl with
      [] -> ALL_TAC (asl,w)
    | (_,cth)::rest ->
        let red = try CONV_RULE(REWRITE_CONV[WORD_AND_0; VAL_WORD_0;
                                             BITVAL_CLAUSES; WORD_ZX_0;
                                             option_DISTINCT; NOT_CLAUSES] THENC
                                WORD_REDUCE_CONV THENC
                                NUM_REDUCE_CONV) cth
                  with Failure _ -> cth in
        if concl red = `F` then CONTR_TAC red (asl,w) else
        let cth = try CONV_RULE(daw_norm_cond_conv rest) cth with Failure _ -> cth in
        try
          let c = concl cth in
          let nc = if is_neg c then dest_neg c else mk_neg c in
          let rest' = filter (fun (_,th) -> daw_arith_ok th) rest in
          let rec has_disj t = match t with
              Comb(Comb(Const(("\\/"|"==>"),_),_),_) -> true
            | Comb(Const("~",_),a) -> has_disj a
            | Comb(Comb(Const("/\\",_),a),b) -> has_disj a || has_disj b
            | _ -> false in
          let atomic = filter (fun (_,th) -> not(has_disj(concl th))) rest' in
          let dec hs = try TAC_PROOF((hs,nc),BSTEP_ARITH_DECIDE_TAC ~rws:[])
                       with Stack_overflow -> failwith "stack" in
          let rec take n l = if n = 0 then [] else match l with h::t -> h::take (n-1) t | [] -> [] in
          let fv = frees nc in
          let disj = take 8 (filter (fun (_,th) -> has_disj(concl th)) rest') in
          let _ = fv in
          let th = try dec atomic with Failure _ ->
                     if disj = [] then failwith "kill"
                     else dec (atomic @ disj) in
          (if is_neg c then CONTR_TAC(MP (NOT_ELIM cth) th)
           else CONTR_TAC(MP (NOT_ELIM th) cth)) (asl,w)
        with Failure _ -> ALL_TAC (asl,w);;

let daw_pc_L = `word(pc + 25596):int64` and daw_pc_T = `word(pc + 25664):int64`;;

(* rewrites for the steps from the assumptions: the instances of           *)
(* DAW_RESET_LIMIT and the facts MIN r 4 = t.                               *)
let daw_step_rws asl =
  mapfilter (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("MIN",_),_),k)),_) when k = `4` -> th
    | Comb(Comb(Const("=",_),Comb(Comb(Comb(Const("COND",_),_),_),_)),
           Comb(Const("word",_),Comb(Comb(Const("MIN",_),_),_))) -> th
    | _ -> fail()) asl;;

(* After a split: the condition (the last assumption) also as arithmetic,   *)
(* with the values of words as numbers where the facts show no wrap-around. *)




(* word_sub a b for two addresses with the same base: word(ta - tb).       *)
let DAW_SUB_CONV asl tm =
  match tm with
    Comb(Comb(Const("word_sub",_),a),b) when type_of a = `:int64` ->
      let ea = DAW_ADDR_CONV a and eb = DAW_ADDR_CONV b in
      let ca = rhs(concl ea) and cb = rhs(concl eb) in
      let base,ta = match ca with
          Comb(Comb(Const("word_add",_),x),Comb(Const("word",_),t)) -> x,t
        | _ -> failwith "DAW_SUB_CONV" in
      let tb = match cb with
          Comb(Comb(Const("word_add",_),y),Comb(Const("word",_),t)) when y = base -> t
        | _ when cb = base -> `0`
        | _ -> failwith "DAW_SUB_CONV" in
      let th =
        if cb = base then ISPECL [base; mk_comb(`word:num->int64`,ta)] DAW_WORD_SUB_ADD_LEFT
        else
          let le = TAC_PROOF((asl,mk_binary "<=" (tb,ta)),DAW_ARITH_TAC) in
          MP (ISPECL [base; ta; tb] DAW_WORD_SUB_ADD_LE) le in
      TRANS (MK_COMB(AP_TERM (rator(rator tm)) ea,eb)) th
  | _ -> failwith "DAW_SUB_CONV";;

(* The values of the registers of the current state rewritten with rws.   *)
let DAW_NORM_REGS_TAC (rws:thm list) : tactic =
  fun (asl,w) ->
    let s = rand w in
    let conv = REWRITE_CONV rws THENC DEPTH_CONV (DAW_SUB_CONV asl) THENC
               TOP_DEPTH_CONV (DAW_ZX_CONV asl) in
    (RULE_ASSUM_TAC(fun th -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s1)),_)
          when s1 = s && is_const c &&
               (let n = fst(dest_const c) in String.length n >= 2 && n.[0] = 'X') ->
          (try CONV_RULE(RAND_CONV conv) th with Failure _ -> th)
      | _ -> th)) (asl,w);;

let rec DAW_RUN_TAC ?(kill=DAW_KILL_TAC) ?(norm=ALL_TAC) ?(rws=[]) ?(calls=[])
                    execth i (leaf:tactic) : tactic = fun g ->
  let r = try bstep_pc_value g with Failure _ -> `T` in
  if !daw_debug then (Printf.printf "STEP %d %s\n%!" i (daw_trunc 200 (string_of_term r)));
  let again = DAW_RUN_TAC ~kill ~norm ~rws ~calls execth in
  if r = `returnaddress:int64` || r = daw_pc_L || r = daw_pc_T then leaf g
  else if is_cond r then
    (BSTEP_SPLIT_PC_TAC THEN TRY kill THEN DAW_NORM_COND_TAC THEN norm THEN again i leaf) g
  else
    match (try Some(assoc r calls) with Failure _ -> None) with
      Some ctac -> let tac,used = ctac i in
                   (tac THEN norm THEN again (i+used) leaf) g
    | None -> (W(fun (asl,_) ->
                 ARM_BSTEP_TAC ~rewrites:(rws @ daw_step_rws asl) execth (i--i) THEN
                 DAW_NORM_REGS_TAC (rws @ daw_step_rws asl)) THEN
               norm THEN again (i+1) leaf) g;;

(* From a cut point: the first step, then the run.                          *)
let DAW_RUN_FROM_TAC ?(kill=DAW_KILL_TAC) ?(norm=ALL_TAC) ?(rws=[]) ?(calls=[])
                     execth (leaf:tactic) : tactic =
  ARM_BSTEP_TAC ~rewrites:rws execth (1--1) THEN DAW_NORM_REGS_TAC rws THEN norm THEN
  DAW_RUN_TAC ~kill ~norm ~rws ~calls execth 2 leaf;;

(* The leaf of a run: the exit (ok from eof_; the decoding fact            *)
(* snappy_decode_tags m inp [] = NONE or = snappy_decode_tags m [] ob among  *)
(* the assumptions), or a cut point L or T (buffer or scratch from X20; the *)
(* stream and the output from the facts of the current state).              *)
let DAW_LEAF_TAC : tactic = fun (asl,w) ->
  let s = rand w in
  let pcv = bstep_pc_value (asl,w) in
  if !daw_debug then
    (Printf.printf "DAW_LEAF at %s (%s), conditions:\n" (string_of_term pcv) (string_of_term s);
     List.iter (fun (_,th) -> let c = concl th in
       if not(vfree_in s c) && can (find_term (fun t -> match t with Const("val",_) -> true | _ -> false)) c
       then Printf.printf "  %s\n" (daw_trunc 300 (string_of_term c))) (rev asl);
     (try let ev = daw_find_fact (fun c -> is_eq c && lhs c = mk_comb(`read events:armstate->(uarch_event)list`,s)) asl in
          let rec jumps t = match t with
              Comb(Comb(Const("CONS",_),Comb(Const("EventJump",_),p)),r) ->
                string_of_term (rand p) :: jumps r
            | Comb(Comb(Const(("CONS"|"APPEND"),_),_),r) -> jumps r
            | _ -> [] in
          Printf.printf "  JUMPS: %s\n" (String.concat " <- " (jumps (rhs(concl ev))))
      with Failure _ -> ());
     Format.print_flush());
  if pcv = `returnaddress:int64` then
    let eof = daw_find_fact (fun c -> is_eq c && lhs c = subst [s,`s:armstate`]
                `read (memory :> bytes8 (word_add d (word 40))) s`) asl in
    if rand(concl eof) = `word 1:byte` then
      let dth = daw_find_fact (fun c -> can (term_match [`m:num`; `inp:byte list`]
                  `snappy_decode_tags m inp [] = snappy_decode_tags m [] ob`) c) asl in
      DAW_EXIT_TAC `T` dth (asl,w)
    else
      let dth = try daw_find_fact (fun c -> c = `snappy_decode_tags m inp [] = NONE`) asl
        with Failure _ ->
          (* from the model fact of the tag: its condition fails *)
          let mth = daw_find_fact (fun c -> is_eq c &&
                      lhs c = `snappy_decode_tags m rest ob` && is_cond(rhs c)) asl in
          let cnd,_ = dest_cond(rhs(concl mth)) in
          let nth = TAC_PROOF((asl,mk_neg cnd),
                      REWRITE_TAC[DE_MORGAN_THM; NOT_LE] THEN DAW_ARITH_TAC) in
          TRANS (ASSUME `snappy_decode_tags m inp [] = snappy_decode_tags m rest ob`)
                (REWRITE_RULE[nth] mth) in
      DAW_EXIT_TAC `F` dth (asl,w)
  else
    let x20 = arm_bstep_eval asl s `read X20 s` in
    let x20 = try rhs(concl(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] x20))
              with Failure _ -> x20 in
    let scratch = (x20 = `word_add d (word 41):int64`) in
    let bth = try daw_bytelist_at asl s x20 with Failure _ ->
      failwith ("DAW_LEAF_TAC: no bytes at " ^ string_of_term x20) in
    let r = rand(concl bth) in
    let decs = mapfilter (fun (_,th) -> let c = concl th in
        match c with
          Comb(Comb(Const("=",_),l),Comb(Comb(Comb(Const("snappy_decode_tags",_),_),r'),ob))
            when l = `snappy_decode_tags m inp []` && r' = r -> ob
        | _ -> fail()) asl in
    let has t = exists (fun (_,th) -> concl th = t) asl in
    let ob = try find (fun ob ->
        has (subst [ob,`ob0:byte list`; s,`s:armstate`]
               `read (memory :> bytelist(out,LENGTH(ob0:byte list))) s = ob0`)) decs
      with Failure _ -> failwith ("DAW_LEAF_TAC: no output for the decoding of " ^
        string_of_term r ^ " among " ^ String.concat "; " (map string_of_term decs)) in
    let isl = (pcv = daw_pc_L) in
    let k = if isl then (if scratch then 3 else 2) else (if scratch then 5 else 4) in
    let lr = mk_comb(`LENGTH:byte list->num`,r) in
    let meas = if isl then mk_binop `(+):num->num->num` (mk_binop `( * ):num->num->num` `2` lr) `1`
               else mk_binop `( * ):num->num->num` `2` lr in
    let iv = if scratch then `0` else daw_offset_from `q:int64` x20 in
    (ASSUME_TAC bth THEN
     DAW_CUT_LEAF_TAC k meas [x20; r; ob; iv] DAW_ARITH_TAC []) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* The calls of RefillTag after a window is used up to ip (in X20 and ip_):  *)
(* the bytes R left at ip (fewer than 5), with the cases R = [] (EMPTY, the  *)
(* end of the stream), refill_ok R (WINDOW, moved to scratch_) and not.     *)
(* ------------------------------------------------------------------------- *)

let daw_canon t = try rhs(concl(DAW_ADDR_CONV t)) with Failure _ -> t;;

(* A fact read c s = v, from one read c s = v0 with v0 = v up to the        *)
(* canonical forms of the addresses and arithmetic.                         *)
let DAW_ENSURE_FACT_TAC (tm:term) : tactic = fun (asl,w) ->
  if exists (fun (_,th) -> concl th = tm) asl then ALL_TAC (asl,w) else
  (SUBGOAL_THEN tm ASSUME_TAC THENL [DAW_WORD_EQ_TAC; ALL_TAC]) (asl,w);;

let DAW_REFILL_CALL_TAC (buf:bool) i =
  let sname = "s" ^ string_of_int i in
  (W(fun (asl,w) ->
    let s = rand w in
    let ipc = daw_canon (arm_bstep_eval asl s `read X20 s`) in
    let blth = daw_bytelist_at asl s ipc in
    let r = rand(concl blth) in
    let dth = daw_find_fact (fun c -> match c with
        Comb(Comb(Const("=",_),l),Comb(Comb(Comb(Const("snappy_decode_tags",_),_),r'),ob))
          -> l = `snappy_decode_tags m inp []` && r' = r
      | _ -> false) asl in
    let ob = rand(rhs(concl dth)) in
    let rd c = subst [s,`s:armstate`] c in
    let p = if buf then `q:int64` else `word_add q (word(LENGTH(inp:byte list))):int64` in
    let nnum = if buf then `LENGTH(inp:byte list)` else `0` in
    let nwd = mk_comb(`word:num->int64`,nnum) in
    let lr = mk_comb(`LENGTH:byte list->num`,r) in
    ASSUME_TAC blth THEN
    DAW_ENSURE_FACT_TAC (rd(subst [ipc,`x:int64`]
      `read (memory :> bytes64 (word_add d (word 8))) s = x`)) THEN
    ASM_CASES_TAC (mk_eq(r,`[]:byte list`)) THENL
     [(* EMPTY *)
      ASSUME_TAC(REWRITE_RULE[LENGTH] (AP_TERM `LENGTH:byte list->num`
                   (ASSUME(mk_eq(r,`[]:byte list`))))) THEN
      DAW_ENSURE_FACT_TAC (rd(subst [ipc,`x:int64`]
        `read (memory :> bytes64 (word_add d (word 16))) s = x`)) THEN
      ASSUME_TAC(SPECL [`word_add q (word(LENGTH(inp:byte list))):int64`; s]
                   DAW_READ_BYTELIST_0) THEN
      ASSUME_TAC(REWRITE_RULE[ASSUME(mk_eq(r,`[]:byte list`))] dth) THEN
      DAW_CALL_GHOST_TAC DAW_REFILL_EMPTY
        (daw_refill_args p nnum nnum ipc `[]:byte list`)
        [SUB_REFL; ARITH_RULE `0 < 5`; snappy_refill_ok; BITVAL_CLAUSES; LENGTH;
         WORD_ADD_0] sname;
      ASM_CASES_TAC (mk_comb(`snappy_refill_ok`,r)) THENL
       [(* WINDOW, moved to scratch_ *)
        DAW_ENSURE_FACT_TAC (rd(subst [ipc,`x:int64`; lr,`l:num`]
          `read (memory :> bytes64 (word_add d (word 16))) s = word_add x (word l)`)) THEN
        SUBGOAL_THEN (mk_binary "<" (lr,`5`)) ASSUME_TAC THENL
         [DAW_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN (mk_eq(mk_comb(mk_comb(`MIN`,lr),`4`),lr)) ASSUME_TAC THENL
         [DAW_ARITH_TAC; ALL_TAC] THEN
        ASSUME_TAC(MP (SPEC lr DAW_RESET_LIMIT)
          (MP (ARITH_RULE (mk_imp(mk_binary "<" (lr,`5`),mk_binary "<" (lr,`2 EXP 63`))))
              (ASSUME (mk_binary "<" (lr,`5`))))) THEN
        DAW_CALL_GHOST_TAC DAW_REFILL_WINDOW
          [`read events s`; `d:int64`; `src:int64`; p; nwd; ipc; r; `pc:num`; `rw:num`;
           `read SP s`; `read X30 s`; `read X19 s`; `read X20 s`; `read X21 s`;
           `read X22 s`; `read X23 s`; `read X24 s`; `read X29 s`;
           `ea:int64`; `el:num`; `ev:num`]
          [ASSUME (mk_binary "<" (lr,`5`)); EQT_INTRO(ASSUME (mk_comb(`snappy_refill_ok`,r)));
           BITVAL_CLAUSES] sname THEN
        DAW_STATE_TAC (fun s' ->
          let bl = daw_find_fact (fun c -> c = subst [s',`s:armstate`; r,`r:byte list`]
                     `read (memory :> bytelist(word_add d (word 41),LENGTH(r:byte list))) s = r`) in
          W(fun (asl,w) -> ASSUME_TAC(MATCH_MP DAW_READ_HD
              (CONJ (bl asl) (ASSUME(mk_neg(mk_eq(r,`[]:byte list`))))))));
        (* WINDOW, the first tag is short *)
        ASSUME_TAC(TRANS dth (MP (SPECL [`m:num`; r; ob] SNAPPY_DECODE_TAGS_SHORT)
          (CONJ (ASSUME(mk_neg(mk_eq(r,`[]:byte list`))))
                (ASSUME(mk_neg(mk_comb(`snappy_refill_ok`,r))))))) THEN
        DAW_ENSURE_FACT_TAC (rd(subst [ipc,`x:int64`; lr,`l:num`]
          `read (memory :> bytes64 (word_add d (word 16))) s = word_add x (word l)`)) THEN
        SUBGOAL_THEN (mk_binary "<" (lr,`5`)) ASSUME_TAC THENL
         [DAW_ARITH_TAC; ALL_TAC] THEN
        DAW_CALL_GHOST_TAC DAW_REFILL_WINDOW
          [`read events s`; `d:int64`; `src:int64`; p; nwd; ipc; r; `pc:num`; `rw:num`;
           `read SP s`; `read X30 s`; `read X19 s`; `read X20 s`; `read X21 s`;
           `read X22 s`; `read X23 s`; `read X24 s`; `read X29 s`;
           `ea:int64`; `el:num`; `ev:num`]
          [ASSUME (mk_binary "<" (lr,`5`));
           EQF_INTRO(ASSUME (mk_neg(mk_comb(`snappy_refill_ok`,r))));
           BITVAL_CLAUSES] sname]])),1;;

(* ------------------------------------------------------------------------- *)
(* The entry: the prologue, RefillTag (EMPTY, k = 0), then L or the exit.    *)
(* ------------------------------------------------------------------------- *)

let DAW_E_GOAL = list_mk_forall(`n:num`::daw_vars, daw_seg daw_entry);;

let DAW_E_CASE_TAC (lt5:bool) (ok:bool) (nil:bool) : tactic =
  let lfact = if lt5 then `LENGTH(inp:byte list) < 5` else `~(LENGTH(inp:byte list) < 5)` in
  let okf = if ok then `snappy_refill_ok(inp:byte list) <=> T` else `snappy_refill_ok(inp:byte list) <=> F` in
  let nilf = if nil then `(inp:byte list = []) <=> T` else `(inp:byte list = []) <=> F` in
  SUBGOAL_THEN (list_mk_conj [lfact; okf; nilf]) STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    ((ASM_REWRITE_TAC[] THEN NO_TAC) ORELSE
     (ASM_REWRITE_TAC[snappy_refill_ok] THEN NO_TAC) ORELSE DAW_ARITH_TAC ORELSE
     (REWRITE_TAC[] THEN MATCH_MP_TAC SNAPPY_REFILL_OK_5 THEN DAW_ARITH_TAC));
    ALL_TAC] THEN
  DAW_INIT_TAC THEN
  ARM_BSTEP_TAC ~rewrites:[WORD_SUB_0] daw_exec (1--18) THEN
  (if nil then DAW_STATE_TAC (fun s -> ASSUME_TAC(SPECL [`q:int64`; s] (REWRITE_RULE[GSYM(INST_TYPE [`:byte`,`:A`] (CONJUNCT1 LENGTH))] DAW_READ_BYTELIST_0)))
   else ALL_TAC) THEN
  DAW_CALL_TAC DAW_REFILL_EMPTY
    (daw_refill_args `q:int64` `LENGTH(inp:byte list)` `0` `ip:int64` `inp:byte list`)
    [ASSUME lfact; ASSUME okf; ASSUME nilf; BITVAL_CLAUSES] "s19";;

let DAW_E_TAC : tactic =
  DAW_START_TAC THEN
  ASM_CASES_TAC `inp:byte list = []` THENL
   [(* the empty stream: RefillTag fails, eof_ *)
    SUBGOAL_THEN `LENGTH(inp:byte list) = 0` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[LENGTH]; ALL_TAC] THEN
    DAW_E_CASE_TAC true false true THEN
    ARM_BSTEP_TAC daw_exec (20--27) THEN DAW_NIL_OUT_TAC THEN
    DAW_EXIT_TAC `T` (REWRITE_CONV[ASSUME `inp:byte list = []`]
                        `snappy_decode_tags m inp []`);
    ALL_TAC] THEN
  ASM_CASES_TAC `LENGTH(inp:byte list) < 5` THENL
   [ASM_CASES_TAC `snappy_refill_ok(inp:byte list)` THENL
     [(* the scratch state *)
      DAW_E_CASE_TAC true true false THEN
      SUBGOAL_THEN `MIN (LENGTH(inp:byte list)) 4 = LENGTH inp` ASSUME_TAC THENL
       [DAW_ARITH_TAC; ALL_TAC] THEN
      ARM_BSTEP_TAC ~rewrites:[DAW_WORD_SUB_ADD_ADD;
         MP (SPEC `LENGTH(inp:byte list)` DAW_RESET_LIMIT)
            (MP (ARITH_RULE `LENGTH(inp:byte list) < 2 EXP 63 ==> LENGTH inp < 2 EXP 63`)
                (ASSUME `LENGTH(inp:byte list) < 2 EXP 63`))] daw_exec (20--34) THEN
      DAW_NIL_OUT_TAC THEN
      DAW_CUT_LEAF_TAC 3 `2 * LENGTH(inp:byte list) + 1`
        [`word_add d (word 41):int64`; `inp:byte list`; `[]:byte list`; `0`]
        DAW_ARITH_TAC [LENGTH; WORD_ADD_0; BITVAL_CLAUSES];
      (* RefillTag fails: the first tag is short *)
      DAW_E_CASE_TAC true false false THEN
      ARM_BSTEP_TAC daw_exec (20--27) THEN DAW_NIL_OUT_TAC THEN
      DAW_EXIT_TAC `F` (MATCH_MP SNAPPY_DECODE_TAGS_SHORT
                         (CONJ (ASSUME `~(inp:byte list = [])`)
                               (ASSUME `~snappy_refill_ok(inp:byte list)`)))];
    (* the buffer state *)
    DAW_E_CASE_TAC false true false THEN
    SUBGOAL_THEN `MIN (LENGTH(inp:byte list)) 4 = 4` ASSUME_TAC THENL
     [DAW_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `memrange(q:int64,1) SUBSET memrange(q,LENGTH(inp:byte list))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC MEMRANGE_PREFIX_SUBSET THEN DAW_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `word_sub (word_add q (word(LENGTH(inp:byte list)))) (word 4):int64 =
                  word_add q (word(LENGTH inp - 4))` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC] THEN
      SUBGOAL_THEN `LENGTH(inp:byte list) = (LENGTH inp - 4) + 4` MP_TAC THENL
       [DAW_ARITH_TAC; DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV o RAND_CONV) [th])] THEN
      REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ARM_BSTEP_TAC ~rewrites:[DAW_WORD_SUB_ADD_LEFT;
       MP (SPEC `LENGTH(inp:byte list)` DAW_RESET_LIMIT)
          (MP (ARITH_RULE `LENGTH(inp:byte list) < 2 EXP 63 ==> LENGTH inp < 2 EXP 63`)
              (ASSUME `LENGTH(inp:byte list) < 2 EXP 63`))] daw_exec (20--34) THEN
    DAW_NIL_OUT_TAC THEN
    DAW_CUT_LEAF_TAC 2 `2 * LENGTH(inp:byte list) + 1`
      [`q:int64`; `inp:byte list`; `[]:byte list`; `0`]
      DAW_ARITH_TAC [LENGTH; WORD_ADD_0; BITVAL_CLAUSES]];;

(* ------------------------------------------------------------------------- *)
(* L (loop1): DecompressBranchless, then T, or RefillTag and T or the exit.  *)
(* ------------------------------------------------------------------------- *)

let DAW_LB_GOAL = list_mk_forall(`n:num`::daw_vars, daw_seg daw_lb);;
let DAW_LS_GOAL = list_mk_forall(`n:num`::daw_vars, daw_seg daw_ls);;
let DAW_TB_GOAL = list_mk_forall(`n:num`::daw_vars, daw_seg daw_tb);;
let DAW_TS_GOAL = list_mk_forall(`n:num`::daw_vars, daw_seg daw_ts);;

let DAW_BRANCHLESS = SNAPPY_DECOMPRESS_BRANCHLESS_CHARP_GCC12_O2_IMAGE_SUBROUTINE_SAFE;;

let daw_find_fact (p:term -> bool) asl = snd(find (fun (_,th) -> p(concl th)) asl);;

(* The state at a cut point, the facts about the regions of the window.    *)
let DAW_CUT_START_TAC (buf:bool) : tactic =
  DAW_START_TAC THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `ipv:int64` (X_CHOOSE_THEN `rest:byte list`
    (X_CHOOSE_THEN `ob:byte list` (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `ipv:int64`)) THEN
  ELF_RELOCATED_DATA_TAC ~defs:[snappy_libsnappy_gcc12_O2_relocated]
     ~select:(elf_slots_importing ["memmove"; "memcpy"]) THEN
  ELF_RELOCATED_DATA_TAC ~defs:[snappy_libsnappy_gcc12_O2_relocated]
     ~select:(elf_slots_at [0x1fc98; 0x1fca0]) THEN
  (* the nonoverlapping facts also as DISJOINT facts, for the orthogonality *)
  (* of regions within them (footprint_orthogonality)                       *)
  W(fun (asl,w) ->
    let ds = mapfilter (fun (_,th) -> match concl th with
        Comb(Comb(Const("nonoverlapping",_),_),_) ->
          (match frees(concl th) with _ ->
             if exists (fun v -> type_of v = `:armstate`) (frees(concl th)) then fail()
             else REWRITE_RULE[NONOVERLAPPING_MEMRANGE] th)
      | _ -> fail()) asl in
    MAP_EVERY ASSUME_TAC ds) THEN
  SUBGOAL_THEN `~(out:int64 = word 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_0]) THEN DAW_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(val(out:int64) = 0)` ASSUME_TAC THENL
   [DAW_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(out:int64) + m < 2 EXP 64` ASSUME_TAC THENL
   [DAW_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(rest:byte list) < 2 EXP 63` ASSUME_TAC THENL
   [DAW_ARITH_TAC; ALL_TAC] THEN
  (if buf then
     let base = `q:int64` and n = `LENGTH(inp:byte list)` and off = `i:num` in
     SUBGOAL_THEN `i + LENGTH(rest:byte list) <= LENGTH(inp:byte list)` ASSUME_TAC THENL
      [DAW_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `val(word_add q (word i):int64) + LENGTH(rest:byte list) < 2 EXP 64`
       ASSUME_TAC THENL
      [MATCH_MP_TAC DAW_VAL_OFFSET THEN EXISTS_TAC n THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
     ASSUME_TAC(MP (ISPECL [base; n; off; `LENGTH(rest:byte list)`] DAW_MEMRANGE_SUB)
                   (ASSUME `i + LENGTH(rest:byte list) <= LENGTH(inp:byte list)`)) THEN
     W(fun (asl,w) ->
       let novs = mapfilter (fun (_,th) -> match concl th with
           Comb(Comb(Const("nonoverlapping",_),p1),_) when p1 = mk_pair(base,n) ->
             MATCH_MP DAW_NONOVERLAPPING_SUB
               (CONJ th (ASSUME `i + LENGTH(rest:byte list) <= LENGTH(inp:byte list)`))
         | _ -> fail()) asl in
       MAP_EVERY ASSUME_TAC novs)
   else
     let le = `41 + LENGTH(rest:byte list) <= 48` in
     SUBGOAL_THEN le ASSUME_TAC THENL [DAW_ARITH_TAC; ALL_TAC] THEN
     ASSUME_TAC(MP (ISPEC `d:int64` DAW_SCRATCH_NOWRAP) (ASSUME `aligned 8 (d:int64)`)) THEN
     SUBGOAL_THEN `val(word_add d (word 41):int64) + LENGTH(rest:byte list) < 2 EXP 64`
       ASSUME_TAC THENL [DAW_ARITH_TAC; ALL_TAC] THEN
     MAP_EVERY (fun j -> ASSUME_TAC(CONV_RULE(LAND_CONV(RAND_CONV(RAND_CONV(RAND_CONV
         NUM_REDUCE_CONV))))
        (MP (SPECL [`d:int64`; mk_small_numeral j] DAW_SCRATCH_VAL)
            (CONJ (MP (ISPEC `d:int64` DAW_SCRATCH_NOWRAP) (ASSUME `aligned 8 (d:int64)`))
                  (ARITH_RULE(mk_binary "<=" (mk_small_numeral j,`5`))))))) [1;2;3;4;5] THEN
     ASSUME_TAC(MP (ISPECL [`d:int64`; `48`; `41`; `LENGTH(rest:byte list)`] DAW_MEMRANGE_SUB)
                   (ASSUME le)) THEN
     W(fun (asl,w) ->
       let novs = mapfilter (fun (_,th) -> match concl th with
           Comb(Comb(Const("nonoverlapping",_),p1),_) when p1 = `d:int64,48` ->
             MATCH_MP DAW_NONOVERLAPPING_SUB (CONJ th (ASSUME le))
         | _ -> fail()) asl in
       MAP_EVERY ASSUME_TAC novs));;

(* The call of DecompressBranchless at L + 0x24.                           *)
let DAW_DB_CALL_TAC (ipv:term) i =
  (W(fun (asl,w) ->
     DAW_CALL_GHOST_TAC DAW_BRANCHLESS
       [`read events s`; ipv; `rest:byte list`; `out:int64`; `ob:byte list`;
        `m:num`; `pc:num`; `rw:num`; `read SP s`; `read X30 s`;
        `read X19 s`; `read X20 s`; `read X21 s`; `read X22 s`; `read X23 s`;
        `read X24 s`; `read X25 s`; `read X26 s`; `read X27 s`; `read X28 s`;
        `read X29 s`; `ea:int64`; `el:num`; `ev:num`] []
       ("s" ^ string_of_int i))),1;;

(* After DecompressBranchless: the stream and the output after its tags.     *)
(* Gives LENGTH out' <= m, LENGTH inp' <= LENGTH rest, the decoding from     *)
(* (inp', out') and the bytes of inp' at ip' = ipv + (LENGTH rest - LENGTH   *)
(* inp') in the current state; returns (inp', out') to the continuation.     *)
let DAW_POST_DB_TAC (ipv:term) (k:term -> term -> tactic) : tactic =
  W(fun (asl,w) ->
    let s = rand w in
    let sth = daw_find_fact (fun c ->
      can (term_match [] `snappy_steps kk m (rest:byte list,ob:byte list) = SOME(a,b)`) c &&
      rand(lhs c) = `rest:byte list,ob:byte list`) asl in
    let inp',out' = dest_pair(rand(rhs(concl sth))) in
    let sm = MATCH_MP SNAPPY_STEPS_SOME sth in
    let dec = TRANS (ASSUME `snappy_decode_tags m inp [] = snappy_decode_tags m rest ob`)
                    (MATCH_MP SNAPPY_STEPS_DECODE_TAGS sth) in
    let lom = MP (CONJUNCT2(CONJUNCT2 sm)) (ASSUME `LENGTH(ob:byte list) <= m`) in
    let bl = daw_find_fact (fun c -> c = subst [ipv,`a:int64`; s,`s:armstate`]
               `read (memory :> bytelist(a,LENGTH(rest:byte list))) s = rest`) asl in
    ASSUME_TAC dec THEN ASSUME_TAC lom THEN
    X_CHOOSE_THEN `hh:byte list` (fun hth ->
      let ath = CONJUNCT1 hth in
      ASSUME_TAC(MATCH_MP DAW_BYTELIST_SUFFIX (CONJ bl ath)) THEN
      ASSUME_TAC(MATCH_MP (ARITH_RULE `a:num = b + c ==> c <= a`)
                   (REWRITE_RULE[LENGTH_APPEND]
                      (AP_TERM `LENGTH:byte list->num` ath))))
      (CONJUNCT1 sm) THEN
    k inp' out');;

let DAW_SLOP_TH = MP (SPECL [`out:int64`; `m:num`] DAW_SLOP)
  (MP (ARITH_RULE `m < 2 EXP 32 ==> m < 2 EXP 64`) (ASSUME `m < 2 EXP 32`));;

let daw_rws = [DAW_WORD_SUB_ADD_LEFT; DAW_WORD_SUB_ADD_ADD; DAW_WORD_ADD_SUB_CANCEL;
               DAW_SLOP_TH];;

let daw_pc_db = `word(pc + 24656):int64` and daw_pc_refill = `word(pc + 18064):int64`;;

let DAW_L_TAC (buf:bool) : tactic =
  let ipv = if buf then `word_add q (word i):int64` else `word_add d (word 41):int64` in
  let post_split inp' out' =
    if buf then ASM_CASES_TAC (mk_binary "<" (mk_comb(`LENGTH:byte list->num`,inp'),`5`)) THENL
      [ALL_TAC;
       W(fun (asl,w) ->
         let s = rand w in
         let bl = daw_find_fact (fun c -> match c with
             Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
               Comb(Comb(Const(":>",_),Const("memory",_)),
                    Comb(Const("bytelist",_),Comb(Comb(Const(",",_),a),Comb(Const("LENGTH",_),r))))),s1)),r')
               -> s1 = s && r = inp' && r' = inp'
           | _ -> false) asl in
         let nn = MP (ARITH_RULE (mk_imp(mk_neg(mk_binary "<" (mk_comb(`LENGTH:byte list->num`,inp'),`5`)),
                     mk_neg(mk_eq(mk_comb(`LENGTH:byte list->num`,inp'),`0`)))))
                     (ASSUME(mk_neg(mk_binary "<" (mk_comb(`LENGTH:byte list->num`,inp'),`5`))))
         in ASSUME_TAC(MATCH_MP DAW_READ_HD (CONJ bl (REWRITE_RULE[LENGTH_EQ_NIL] nn))))]
    else ALL_TAC in
  let db_call i =
    let tac,used = DAW_DB_CALL_TAC ipv i in
    (tac THEN DAW_POST_DB_TAC ipv post_split),used in
  DAW_CUT_START_TAC buf THEN
  DAW_RUN_FROM_TAC ~rws:daw_rws
    ~calls:[daw_pc_db, db_call; daw_pc_refill, DAW_REFILL_CALL_TAC buf]
    daw_exec DAW_LEAF_TAC;;

(* ------------------------------------------------------------------------- *)
(* T (join3): one tag of the slow path.                                      *)
(* ------------------------------------------------------------------------- *)

(* The bytes after the tag byte: TL rest at ipv + 1, and the 32 bits there   *)
(* (ldur w24, [x20, #1]) as a variable b32 with its low k bytes.             *)
let DAW_T_PREP_TAC (buf:bool) (ks:int list) : tactic =
  let ipv = if buf then `word_add q (word i):int64` else `word_add d (word 41):int64` in
  let ipv1 = if buf then `word_add q (word (i + 1)):int64` else `word_add d (word 42):int64` in
  W(fun (asl,w) ->
    let s = rand w in
    let bl = daw_find_fact (fun c -> c = subst [ipv,`a:int64`; s,`s:armstate`]
               `read (memory :> bytelist(a,LENGTH(rest:byte list))) s = rest`) asl in
    let l1 = MP (ARITH_RULE `~(LENGTH(rest:byte list) = 0) ==> 1 <= LENGTH rest`)
                (REWRITE_RULE[GSYM LENGTH_EQ_NIL] (ASSUME `~(rest:byte list = [])`)) in
    let th1 = MATCH_MP READ_BYTELIST_SUFFIX (CONJ bl l1) in
    let th2 = REWRITE_RULE[GSYM(MATCH_MP DAW_TL_SUB_LIST (ASSUME `~(rest:byte list = [])`));
                           GSYM(MATCH_MP LENGTH_TL (ASSUME `~(rest:byte list = [])`))] th1 in
    let eqa = WORD_RULE(mk_eq(mk_binop `word_add:int64->int64->int64` ipv `word 1:int64`,ipv1)) in
    let th3 = REWRITE_RULE[eqa] th2 in
    ASSUME_TAC th3 THEN ASSUME_TAC l1 THEN
    SUBGOAL_THEN `LENGTH(TL(rest:byte list)) + 1 = LENGTH rest` ASSUME_TAC THENL
     [REWRITE_TAC[MATCH_MP LENGTH_TL (ASSUME `~(rest:byte list = [])`)] THEN DAW_ARITH_TAC; ALL_TAC] THEN
    X_CHOOSE_THEN `b32:int32` ASSUME_TAC
      (prove(mk_exists(`b32:int32`,mk_eq(subst [ipv1,`a:int64`; s,`s:armstate`]
               `read (memory :> bytes32 a) s`,`b32:int32`)),
             MESON_TAC[])) THEN
    MAP_EVERY (fun k ->
      let kt = mk_small_numeral k in
      let le = subst [kt,`k:num`] `k <= LENGTH(TL(rest:byte list))` in
      W(fun (asl,w) ->
        try
          let lth = TAC_PROOF((asl,le),DAW_ARITH_TAC) in
          let bth = daw_find_fact (fun c -> c = subst [ipv1,`a:int64`; s,`s:armstate`]
                      `read (memory :> bytes32 a) s = b32`) asl in
          let mth = MATCH_MP DAW_BYTES32_LOW
                      (CONJ th3 (CONJ (ARITH_RULE(subst [kt,`k:num`] `k <= 4`)) lth)) in
          let mth = REWRITE_RULE[bth] mth in
          let wth = MATCH_MP DAW_WORD_AND_MASK32
                      (CONJ mth (ARITH_RULE(subst [kt,`k:num`] `k <= 4`))) in
          ASSUME_TAC lth THEN ASSUME_TAC mth THEN
          ASSUME_TAC(CONV_RULE(LAND_CONV(RAND_CONV(RAND_CONV NUM_REDUCE_CONV))) wth)
        with Failure _ -> ALL_TAC)) ks);;

(* The rewrites of the tag kind k = val c MOD 4.                            *)
let daw_and3_rw k =
  let kt = mk_small_numeral k in
  REWRITE_RULE[ASSUME(subst [kt,`k:num`] `val(HD(rest:byte list)) MOD 4 = k`)]
    (SPEC `HD(rest:byte list)` DAW_TAG_AND3);;

(* Copies with 1- and 2-byte offsets: the table entry and what the code     *)
(* makes of it.                                                             *)
let DAW_T_TABLE_TAC (k:int) : tactic =
  let kt = mk_small_numeral k in
  let kf = ASSUME(subst [kt,`k:num`] `val(HD(rest:byte list)) MOD 4 = k`) in
  let dj = if k = 1 then DISJ1 kf `val(HD(rest:byte list)) MOD 4 = 2`
           else DISJ2 `val(HD(rest:byte list)) MOD 4 = 1` kf in
  DAW_STATE_TAC (fun s ->
    W(fun (asl,w) ->
      let lth = daw_find_fact (fun c -> c = subst [s,`s:armstate`]
         `aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc`) asl in
      ASSUME_TAC(MATCH_MP DAW_LMO_TABLE (CONJ lth dj)))) THEN
  ASSUME_TAC(REWRITE_RULE[kf; ARITH_EQ] (MATCH_MP DAW_LMO_CODE dj)) THEN
  ASSUME_TAC(SPEC `HD(rest:byte list)` DAW_VAL_WORD_ZX_BYTE);;

(* ------------------------------------------------------------------------- *)
(* T: the copies.                                                            *)
(* ------------------------------------------------------------------------- *)

let daw_pc_memmove = `word(pc + 12224):int64`
and daw_pc_memcpy = `word(pc + 12080):int64`
and daw_pc_ic = `word(pc + 12544):int64`;;

let DAW_INCREMENTAL_COPY = SNAPPY_INCREMENTAL_COPY_GCC12_O2_IMAGE_SUBROUTINE_SAFE;;

let daw_out_regions = [`d:int64,48`; `wr:int64,32`; `src:int64,24`;
  `word_sub sp (word 400):int64,400`;
  `word pc:int64,libsnappy_rw + libsnappy_rw_size`; `ea:int64,el:num`];;

(* For a region (out + t, k) of the output with t + k <= m by arithmetic: it *)
(* is within (out, m), disjoint from the other regions, from the window     *)
(* (ipv, LENGTH rest) and, if L <= t, from the output so far (out, L).       *)
let DAW_OUT_REGION_TAC (t:term) (k:term) (ipv:term) (lob:term) : tactic =
  fun (asl,w) ->
    let le = mk_binary "<=" (mk_binop `(+):num->num->num` t k,`m:num`) in
    let lth = TAC_PROOF((asl,le),DAW_ARITH_TAC) in
    let a = mk_binop `word_add:int64->int64->int64` `out:int64` (mk_comb(`word:num->int64`,t)) in
    let sub = MP (ISPECL [`out:int64`; `m:num`; t; k] DAW_MEMRANGE_SUB) lth in
    let novs = mapfilter (fun r ->
        let th = daw_find_fact (fun c -> c = mk_icomb(mk_icomb(`nonoverlapping:int64#num->int64#num->bool`,
                   `out:int64,m:num`),r)) asl in
        MATCH_MP DAW_NONOVERLAPPING_SUB (CONJ th lth)) daw_out_regions in
    let win = try
        let th = daw_find_fact (fun c -> c = mk_icomb(mk_icomb(`nonoverlapping:int64#num->int64#num->bool`,
                   mk_pair(ipv,`LENGTH(rest:byte list)`)),`out:int64,m:num`)) asl in
        let w1 = MATCH_MP DAW_NONOVERLAPPING_SUB_R (CONJ th lth) in
        (* and the bytes after the tag byte, TL rest at ipv + 1 *)
        let w2 = try
            let le = TAC_PROOF((asl,`1 + LENGTH(TL(rest:byte list)) <= LENGTH rest`),DAW_ARITH_TAC) in
            let th2 = MATCH_MP DAW_NONOVERLAPPING_SUB (CONJ w1 le) in
            let a1 = lhand(lhand(concl th2)) in
            [CONV_RULE(LAND_CONV(LAND_CONV(K(DAW_ADDR_CONV a1)))) th2]
          with Failure _ -> [] in
        w1 :: w2
      with Failure _ -> [] in
    let prev = try
        let le2 = mk_binary "<=" (lob,t) in
        let _ = TAC_PROOF((asl,le2),DAW_ARITH_TAC) in
        let nw = mk_binary "<=" (mk_binop `(+):num->num->num` (mk_binop `(+):num->num->num`
                   `val(out:int64)` lob) k,`2 EXP 64`) in
        let nth = TAC_PROOF((asl,nw),DAW_ARITH_TAC) in
        let th = MATCH_MP DAW_NONOVERLAPPING_ADJ nth in
        if t = lob then [th] else []
      with Failure _ -> [] in
    MAP_EVERY ASSUME_TAC (sub :: novs @ win @ prev) (asl,w);;

(* The facts of the model after a copy (off, len) from (rest, ob) with the  *)
(* stream rest' after the tag: the length and the decoding (its condition   *)
(* by arithmetic from the branch conditions).                               *)
let DAW_AFTER_COPY_TAC (mth:thm) : tactic =
  (* mth: snappy_decode_tags m rest ob = if C then snappy_decode_tags m r' o' else NONE *)
  fun (asl,w) ->
    let cnd,(yes,_) = dest_cond(rhs(concl mth)) in
    let cth = TAC_PROOF((asl,cnd),REPEAT CONJ_TAC THEN DAW_ARITH_TAC) in
    let dth = TRANS (ASSUME `snappy_decode_tags m inp [] = snappy_decode_tags m rest ob`)
                    (REWRITE_RULE[cth] mth) in
    let o' = rand yes and r' = rand(rator yes) in
    let lth = try [ISPECL [rand(rator(rator o')); rand(rator o'); rand o'] LENGTH_SNAPPY_COPY]
              with Failure _ -> [] in
    let rth = try [ISPECL [rand r'; lhand(rand(rator r'))] SNAPPY_LENGTH_SUB_LIST_SUFFIX]
              with Failure _ -> [] in
    (* the bytes of the stream after the tag, at the address after its bytes *)
    let bth = try
        let s = rand w in
        let tl = rand r' and j = lhand(rand(rator r')) in
        let tb = daw_find_fact (fun c -> match c with
            Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
                 Comb(Comb(Const(":>",_),Const("memory",_)),
                      Comb(Const("bytelist",_),Comb(Comb(Const(",",_),_),
                           Comb(Const("LENGTH",_),l))))),s1)),l') ->
              s1 = s && l = tl && l' = tl
          | _ -> false) asl in
        let jle = TAC_PROOF((asl,mk_binary "<=" (j,mk_comb(`LENGTH:byte list->num`,tl))),
                    DAW_ARITH_TAC) in
        let sfx = MATCH_MP READ_BYTELIST_SUFFIX (CONJ tb jle) in
        let eq = ISPECL [tl; j] SNAPPY_LENGTH_SUB_LIST_SUFFIX in
        [CONV_RULE(LAND_CONV(RATOR_CONV(RAND_CONV(RAND_CONV(RAND_CONV(RAND_CONV
           (K(SYM eq)))))))) sfx]
      with Failure _ -> [] in
    let lm = try
        let l = hd lth in
        [TAC_PROOF((asl,mk_binary "<=" (mk_comb(`LENGTH:byte list->num`,o'),`m:num`)),
                   REWRITE_TAC[l] THEN DAW_ARITH_TAC)]
      with Failure _ -> [] in
    MAP_EVERY ASSUME_TAC (dth :: lth @ rth @ bth @ lm) (asl,w);;

let daw_model_fact asl = daw_find_fact (fun c -> is_eq c &&
  lhs c = `snappy_decode_tags m rest ob` && is_cond(rhs c)) asl;;

let DAW_MEMMOVE_COPY_TAC (ipv:term) i =
  let sname = "s" ^ string_of_int (i + 4) in
  (ARM_BSTEP_PLT_STUB_TAC daw_exec THEN W(fun (asl,w) ->
     let s = rand w in
     let lob = `LENGTH(ob:byte list)` in
     let offv = `off:num` and lenv = `len:num` in
     let srcn = mk_binop `(-):num->num->num` lob offv in
     let src = mk_binop `word_add:int64->int64->int64` `out:int64` (mk_comb(`word:num->int64`,srcn)) in
     let le = TAC_PROOF((asl,mk_binary "<=" (offv,lob)),DAW_ARITH_TAC) in
     let seq = MP (ISPECL [`out:int64`; lob; offv] DAW_WORD_ADD_SUB_NUM) le in
     let srcraw = arm_bstep_eval asl s `read X1 s` in
     DAW_OUT_REGION_TAC srcn `64` ipv lob THEN
     DAW_OUT_REGION_TAC lob `64` ipv lob THEN
     X_CHOOSE_THEN `x64:num` (fun th -> ASSUME_TAC th THEN
         ASSUME_TAC(REWRITE_RULE[seq] th))
       (prove(mk_exists(`x64:num`,mk_eq(subst [srcraw,`a:int64`; s,`s:armstate`]
                `read (memory :> bytes(a,64)) s`,`x64:num`)),MESON_TAC[])) THEN
     W(fun (asl,w) ->
       (* the region facts also for the address as the code has it *)
       let sub = daw_find_fact (fun c -> c = mk_icomb(mk_icomb(`(SUBSET):(int64->bool)->(int64->bool)->bool`,
                   mk_icomb(`memrange:int64#num->int64->bool`,mk_pair(src,`64`))),`memrange(out:int64,m)`)) asl in
       ASSUME_TAC(REWRITE_RULE[GSYM seq] sub)) THEN
     W(fun (asl,w) ->
       let bl = daw_find_fact (fun c -> c = subst [s,`s:armstate`]
                  `read (memory :> bytelist(out,LENGTH(ob:byte list))) s = ob`) asl in
       let xb = daw_find_fact (fun c -> c = subst [src,`a:int64`; s,`s:armstate`]
                  `read (memory :> bytes(a,64)) s = x64`) asl in
       let ar = TAC_PROOF((asl,`len <= off /\ off <= LENGTH(ob:byte list) /\ len <= 64`),
                          REPEAT CONJ_TAC THEN DAW_ARITH_TAC) in
       ASSUME_TAC(MATCH_MP DAW_COPY_SRC (CONJ bl (CONJ xb ar)))) THEN
     USE_THEN "H_MEMMOVE" (fun th ->
       ARM_BSTEP_CONTRACT_TAC daw_exec th
        [`read events s`; `read X0 s`; `read X1 s`; `read X2 s`; `x64:num`;
         `read X30 s`] sname) THEN
     MEMACCESS_INBOUNDS_TO_INSET_TAC THEN
     DAW_STATE_TAC (fun s' -> W(fun (asl,w) ->
       let bl = daw_find_fact (fun c -> c = subst [s',`s:armstate`]
                  `read (memory :> bytelist(out,LENGTH(ob:byte list))) s = ob`) asl in
       let xb = daw_find_fact (fun c -> c = subst [s',`s:armstate`]
                  `read (memory :> bytes(word_add out (word(LENGTH(ob:byte list))),64)) s = x64`) asl in
       let xm = daw_find_fact (fun c -> can (term_match [`x64:num`] `x64 MOD 2 EXP (8 * len) = y`) c) asl in
       let ar = TAC_PROOF((asl,`len <= off /\ off <= LENGTH(ob:byte list) /\ len <= 64`),
                          REPEAT CONJ_TAC THEN DAW_ARITH_TAC) in
       ASSUME_TAC(MATCH_MP DAW_COPY_MEMMOVE (CONJ bl (CONJ xb (CONJ xm ar)))))) THEN
     W(fun (asl,w) -> DAW_AFTER_COPY_TAC (daw_model_fact asl)))),5;;

let DAW_IC_COPY_TAC (ipv:term) i =
  let sname = "s" ^ string_of_int i in
  (W(fun (asl,w) ->
     let s = rand w in
     let lob = `LENGTH(ob:byte list)` in
     let b = mk_binop `(-):num->num->num` `m:num` lob in
     let op = mk_binop `word_add:int64->int64->int64` `out:int64` (mk_comb(`word:num->int64`,lob)) in
     let bl = mk_binop `word_add:int64->int64->int64` op (mk_comb(`word:num->int64`,b)) in
     DAW_ENSURE_FACT_TAC (subst [bl,`x:int64`; s,`s:armstate`] `read X3 s = x`) THEN
     MAP_EVERY (fun t -> SUBGOAL_THEN (subst [b,`b:num`] t) ASSUME_TAC THENL
                          [DAW_ARITH_TAC; ALL_TAC])
       [`1 <= off`; `off <= LENGTH(ob:byte list)`; `1 <= len`; `len <= 64`; `len <= b`;
        `17 <= val(out:int64) + LENGTH(ob:byte list) + b`;
        `val(out:int64) + LENGTH(ob:byte list) + b < 2 EXP 64`;
        `val(out:int64) + LENGTH(ob:byte list) + 64 < 2 EXP 64`] THEN
     DAW_OUT_REGION_TAC lob b ipv lob THEN
     W(fun (asl,w) ->
       (* the source of the copy, op - off, within the output *)
       let le = TAC_PROOF((asl,`off <= LENGTH(ob:byte list)`),DAW_ARITH_TAC) in
       let seq = MP (ISPECL [`out:int64`; lob; `off:num`] DAW_WORD_ADD_SUB_NUM) le in
       let t = mk_binop `(-):num->num->num` lob `off:num` in
       let k = mk_binop `(+):num->num->num` `off:num` b in
       let le2 = TAC_PROOF((asl,mk_binary "<=" (mk_binop `(+):num->num->num` t k,`m:num`)),
                   DAW_ARITH_TAC) in
       let sub = MP (ISPECL [`out:int64`; `m:num`; t; k] DAW_MEMRANGE_SUB) le2 in
       ASSUME_TAC(REWRITE_RULE[GSYM seq] sub)) THEN
     W(fun (asl,w) ->
       let nv = daw_find_fact (fun c -> c = mk_icomb(mk_icomb(`nonoverlapping:int64#num->int64#num->bool`,
                  mk_pair(op,b)),`word pc:int64,libsnappy_rw + libsnappy_rw_size`)) asl in
       ASSUME_TAC(MP (ISPECL [`word pc:int64`; `libsnappy_rw + libsnappy_rw_size`;
                              `libsnappy_size:num`; op; b] NONOVERLAPPING_PREFIX_RIGHT)
                     (CONJ nv (ARITH_RULE
                       `libsnappy_size <= libsnappy_rw + libsnappy_rw_size`)))) THEN
     DAW_CALL_TAC DAW_INCREMENTAL_COPY
       [`read events s`; `read X0 s`; `read X1 s`; `read X2 s`; bl; `out:int64`;
        `ob:byte list`; `off:num`; `len:num`; b; `pc:num`; `read X30 s`] [] sname THEN
     DAW_STATE_TAC (fun s' -> W(fun (asl,w) ->
       let th = daw_find_fact (fun c -> c = subst [s',`s:armstate`]
          `read (memory :> bytelist(out,LENGTH(ob:byte list) + len)) s = snappy_copy off len ob`) asl in
       ASSUME_TAC(REWRITE_RULE[GSYM LENGTH_SNAPPY_COPY] th))) THEN
     W(fun (asl,w) -> DAW_AFTER_COPY_TAC (daw_model_fact asl)))),1;;

(* Copies with 1- and 2-byte offsets (kind k = 1, 2).                       *)
let DAW_T_COPY12_TAC (buf:bool) (k:int) : tactic =
  let ipv = if buf then `word_add q (word i):int64` else `word_add d (word 41):int64` in
  let kt = mk_small_numeral k in
  let kf = subst [kt,`k:num`] `val(HD(rest:byte list)) MOD 4 = k` in
  let nbf = subst [kt,`k:num`] `k <= LENGTH(TL(rest:byte list))` in
  let nilf = `~(rest:byte list = [])` in
  SUBGOAL_THEN (subst [kt,`k:num`] `k + 1 <= LENGTH(rest:byte list)`) ASSUME_TAC THENL
   [(if buf then DAW_ARITH_TAC else
     MP_TAC(MATCH_MP DAW_TAG_NEEDED (ASSUME `snappy_refill_ok(rest:byte list)`)) THEN
     ASM_REWRITE_TAC[ARITH_EQ] THEN ARITH_TAC); ALL_TAC] THEN
  DAW_T_PREP_TAC buf [k] THEN
  ASSUME_TAC(SPEC `HD(rest:byte list)` DAW_TAG_BOUNDS) THEN
  ASSUME_TAC(CONV_RULE NUM_REDUCE_CONV (MP (SPECL [`TL(rest:byte list)`; kt]
     DAW_NUM_OF_BYTELIST_SUB_BOUND) (ASSUME nbf))) THEN
  DAW_T_TABLE_TAC k THEN
  (if k = 1 then
     SUBGOAL_THEN `num_of_bytelist(SUB_LIST(0,1) (TL(rest:byte list))) +
                   256 * (val(HD rest) DIV 4 DIV 8) < 2 EXP 32`
       (fun th -> ASSUME_TAC(GEN_REWRITE_RULE (RAND_CONV o RAND_CONV) [ADD_SYM]
                    (MATCH_MP DAW_ZX_ADD32 th)) THEN
                  ASSUME_TAC(ONCE_REWRITE_RULE[ADD_SYM] th)) THENL
      [DAW_ARITH_TAC; ALL_TAC]
   else
     SUBGOAL_THEN `num_of_bytelist(SUB_LIST(0,2) (TL(rest:byte list))) < 2 EXP 32`
       (fun th -> ASSUME_TAC(MATCH_MP DAW_ZX_WORD32 th) THEN ASSUME_TAC th) THENL
      [DAW_ARITH_TAC; ALL_TAC]) THEN
  (let dl = if k = 1 then DAW_DECODE_COPY1 else DAW_DECODE_COPY2 in
   let mth = MP (SPECL [`m:num`; `HD(rest:byte list)`; `TL(rest:byte list)`; `ob:byte list`] dl)
                (CONJ (ASSUME kf) (if k = 1 then ASSUME `1 <= LENGTH(TL(rest:byte list))`
                                   else ASSUME `2 <= LENGTH(TL(rest:byte list))`)) in
   let mth = CONV_RULE(TOP_DEPTH_CONV let_CONV)
               (REWRITE_RULE[SYM(MATCH_MP CONS_HD_TL (ASSUME nilf))] mth) in
   ASSUME_TAC mth) THEN
  (if k = 1 then
     ABBREV_TAC `off = 256 * (val(HD(rest:byte list)) DIV 4 DIV 8) +
                       num_of_bytelist(SUB_LIST(0,1) (TL rest))` THEN
     ABBREV_TAC `len = val(HD(rest:byte list)) DIV 4 MOD 8 + 4`
   else
     ABBREV_TAC `off = num_of_bytelist(SUB_LIST(0,2) (TL(rest:byte list)))` THEN
     ABBREV_TAC `len = val(HD(rest:byte list)) DIV 4 + 1`) THEN
  W(fun (asl,w) ->
    let codes = mapfilter (fun (_,th) ->
        let c = concl th in
        if can (term_match [] `word_and (b:int32) (word k) = word n`) c ||
           can (term_match [] `word_zx (x:int32):int64 = word n`) c ||
           (can (find_term (fun t -> t = `daw_lmo(HD(rest:byte list))`)) c &&
            not(exists (fun v -> type_of v = `:armstate`) (frees c)))
        then th else fail()) asl in
    let codes = flat (map CONJUNCTS codes) in
    let and64 = REWRITE_RULE[ASSUME kf] (SPEC `HD(rest:byte list)` DAW_TAG_AND3_64) in
    DAW_RUN_FROM_TAC ~rws:(daw_rws @ [daw_and3_rw k; and64; WORD_ADD_0] @ codes)
      ~calls:[daw_pc_memmove, DAW_MEMMOVE_COPY_TAC ipv;
              daw_pc_ic, DAW_IC_COPY_TAC ipv;
              daw_pc_refill, DAW_REFILL_CALL_TAC buf]
      daw_exec DAW_LEAF_TAC);;

(* Copies with 4-byte offsets (buffer state only: they need 5 bytes).      *)
let DAW_T_COPY4_TAC : tactic =
  let buf = true in
  let ipv = `word_add q (word i):int64` in
  let kf = `val(HD(rest:byte list)) MOD 4 = 3` in
  let nilf = `~(rest:byte list = [])` in
  SUBGOAL_THEN `4 + 1 <= LENGTH(rest:byte list)` ASSUME_TAC THENL
   [DAW_ARITH_TAC; ALL_TAC] THEN
  DAW_T_PREP_TAC buf [4] THEN
  ASSUME_TAC(SPEC `HD(rest:byte list)` DAW_TAG_BOUNDS) THEN
  ASSUME_TAC(CONV_RULE NUM_REDUCE_CONV (MP (SPECL [`TL(rest:byte list)`; `4`]
     DAW_NUM_OF_BYTELIST_SUB_BOUND) (ASSUME `4 <= LENGTH(TL(rest:byte list))`))) THEN
  W(fun (asl,w) ->
    let mth = daw_find_fact (fun c -> can (term_match [`b32:int32`] `val b32 MOD 2 EXP (8 * 4) = n`) c) asl in
    ASSUME_TAC(MATCH_MP DAW_ZX_B32 mth)) THEN
  SUBGOAL_THEN `val(HD(rest:byte list)) DIV 4 + 1 < 2 EXP 32`
    (fun th -> ASSUME_TAC(MATCH_MP DAW_WORD_ADD_ZX1 th)) THENL
   [DAW_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(HD(rest:byte list)) DIV 4 + 1 < 256`
    (fun th -> ASSUME_TAC(MATCH_MP DAW_WORD_AND_255_SMALL th)) THENL
   [DAW_ARITH_TAC; ALL_TAC] THEN
  (let mth = MP (SPECL [`m:num`; `HD(rest:byte list)`; `TL(rest:byte list)`; `ob:byte list`]
                       DAW_DECODE_COPY4) (CONJ (ASSUME kf) (ASSUME `4 <= LENGTH(TL(rest:byte list))`)) in
   let mth = CONV_RULE(TOP_DEPTH_CONV let_CONV)
               (REWRITE_RULE[SYM(MATCH_MP CONS_HD_TL (ASSUME nilf))] mth) in
   ASSUME_TAC mth) THEN
  ABBREV_TAC `off = num_of_bytelist(SUB_LIST(0,4) (TL(rest:byte list)))` THEN
  ABBREV_TAC `len = val(HD(rest:byte list)) DIV 4 + 1` THEN
  W(fun (asl,w) ->
    let codes = mapfilter (fun (_,th) ->
        let c = concl th in
        if can (term_match [] `word_zx (x:int32):int64 = word n`) c ||
           can (term_match [] `word_and (word n:int64) (word 255) = word n`) c
        then th else fail()) asl in
    let and64 = REWRITE_RULE[ASSUME kf] (SPEC `HD(rest:byte list)` DAW_TAG_AND3_64) in
    DAW_RUN_FROM_TAC ~rws:(daw_rws @ [daw_and3_rw 3; and64; SPEC `HD(rest:byte list)` DAW_TAG_USHR2;
                                       WORD_ADD_0] @ codes)
      ~calls:[daw_pc_memmove, DAW_MEMMOVE_COPY_TAC ipv;
              daw_pc_ic, DAW_IC_COPY_TAC ipv;
              daw_pc_refill, DAW_REFILL_CALL_TAC buf]
      daw_exec DAW_LEAF_TAC);;

(* ------------------------------------------------------------------------- *)
(* T: the literals.                                                          *)
(* ------------------------------------------------------------------------- *)

(* Hooks of the run at given PC values (before the instruction there).      *)
let DAW_PC_HOOK_TAC (hooks:(term * tactic) list) : tactic =
  fun g ->
    let r = try bstep_pc_value g with Failure _ -> `T` in
    match (try Some(assoc r hooks) with Failure _ -> None) with
      Some tac -> tac g
    | None -> ALL_TAC g;;

(* The call of memcpy of the literal (or of the bytes left of it): from the *)
(* bytes l at the source (X1), n bytes (X2 = word n), to the output at op.   *)
let DAW_MEMCPY_LIT_TAC (ipv:term) i =
  let sname = "s" ^ string_of_int (i + 4) in
  (ARM_BSTEP_PLT_STUB_TAC daw_exec THEN W(fun (asl,w) ->
     let s = rand w in
     if !daw_debug then List.iter (fun r -> Printf.printf "MEMCPY %s = %s\n%!" r
         (try string_of_term(arm_bstep_eval asl s (parse_term ("read "^r^" s"))) with _ -> "?")) ["X0";"X1";"X2"];
     let x1raw = arm_bstep_eval asl s `read X1 s` in
     let x1 = daw_canon x1raw in
     let n = rand(arm_bstep_eval asl s `read X2 s`) in
     let blth = daw_bytelist_at asl s x1 in
     let l = rand(concl blth) in
     let lob = `LENGTH(ob:byte list)` in
     let nle = TAC_PROOF((asl,mk_binary "<=" (n,mk_comb(`LENGTH:byte list->num`,l))),DAW_ARITH_TAC) in
     let sub = MP (ISPECL [`memory:(armstate,int64->byte)component`; x1; `0`; n;
                           mk_comb(`LENGTH:byte list->num`,l); s] READ_BYTELIST_SUB_LIST)
                  (MP (ARITH_RULE (mk_imp(concl nle,mk_binary "<=" (mk_binop `(+):num->num->num` `0` n,
                          mk_comb(`LENGTH:byte list->num`,l))))) nle) in
     let sub = CONV_RULE(RAND_CONV(REWRITE_CONV[blth]) THENC
                         LAND_CONV(REWRITE_CONV[WORD_ADD_0])) sub in
     let byt = CONJUNCT2(EQ_MP (PART_MATCH lhs READ_BYTELIST_EQ_BYTES (concl sub)) sub) in
     let byt = if x1raw = x1 then byt else
               SUBS[SYM(TRANS (DAW_ADDR_CONV x1raw) (SYM(DAW_ADDR_CONV x1)))] byt in
     let nv = TAC_PROOF((asl,mk_eq(mk_comb(`val:int64->num`,mk_comb(`word:num->int64`,n)),n)),
                REWRITE_TAC[VAL_WORD_EQ_EQ; DIMINDEX_64] THEN DAW_ARITH_TAC) in
     ASSUME_TAC blth THEN ASSUME_TAC byt THEN ASSUME_TAC nv THEN
     DAW_OUT_REGION_TAC lob n ipv lob THEN
     W(fun (asl,w) ->
       (* the source (in the input or scratch_) is disjoint from the destination *)
       let eq = DAW_ADDR_CONV x1 in
       let a' = rhs(concl eq) in
       let b,nb,t = tryfind (fun (b,nb) -> b,nb,daw_offset_from b a')
                      [`q:int64`,`LENGTH(inp:byte list)`; `d:int64`,`48`] in
       let op = mk_binop `word_add:int64->int64->int64` `out:int64` (mk_comb(`word:num->int64`,lob)) in
       let th0 = daw_find_fact (fun c -> c = mk_icomb(mk_icomb(`nonoverlapping:int64#num->int64#num->bool`,
                   mk_pair(b,nb)),`out:int64,m:num`)) asl in
       let le1 = TAC_PROOF((asl,mk_binary "<=" (mk_binop `(+):num->num->num` t n,nb)),DAW_ARITH_TAC) in
       let le2 = TAC_PROOF((asl,mk_binary "<=" (mk_binop `(+):num->num->num` lob n,`m:num`)),DAW_ARITH_TAC) in
       let th1 = MATCH_MP DAW_NONOVERLAPPING_SUB (CONJ th0 le1) in
       let th2 = MATCH_MP DAW_NONOVERLAPPING_SUB_R (CONJ th1 le2) in
       let ad = lhand(lhand(concl th2)) in
       let eq2 = TRANS (DAW_ADDR_CONV ad) (SYM eq) in
       let th3 = CONV_RULE(LAND_CONV(LAND_CONV(K eq2))) th2 in
       ASSUME_TAC th3 THEN ASSUME_TAC(ONCE_REWRITE_RULE[NONOVERLAPPING_SYM] th3)) THEN
     (fun g -> if !daw_debug then print_endline "MEMCPY: call"; ALL_TAC g) THEN
     USE_THEN "H_MEMCPY" (fun th ->
       ARM_BSTEP_CONTRACT_TAC daw_exec th
        [`read events s`; `read X0 s`; `read X1 s`; `read X2 s`;
         mk_comb(`num_of_bytelist`,mk_comb(mk_comb(`SUB_LIST:num#num->byte list->byte list`,
                   mk_pair(`0`,n)),l));
         `read X30 s`] sname) THEN
     (fun g -> if !daw_debug then print_endline "MEMCPY: after"; ALL_TAC g) THEN
     MEMACCESS_INBOUNDS_TO_INSET_TAC THEN
     DAW_STATE_TAC (fun s' -> W(fun (asl,w) ->
       let op = mk_binop `word_add:int64->int64->int64` `out:int64` (mk_comb(`word:num->int64`,lob)) in
       let pl = mk_comb(mk_comb(`SUB_LIST:num#num->byte list->byte list`,mk_pair(`0`,n)),l) in
       let bt = daw_find_fact (fun c -> c = subst [op,`a:int64`; n,`n:num`; pl,`pl:byte list`; s',`s:armstate`]
                  `read (memory :> bytes(a,n)) s = num_of_bytelist pl`) asl in
       let ln = TAC_PROOF((asl,mk_eq(mk_comb(`LENGTH:byte list->num`,pl),n)),
                  REWRITE_TAC[LENGTH_SUB_LIST] THEN DAW_ARITH_TAC) in
       let blo = EQ_MP (SYM(ISPECL [op; pl; n; s'] READ_BYTELIST_EQ_BYTES)) (CONJ ln bt) in
       let blo = CONV_RULE(LAND_CONV(RATOR_CONV(RAND_CONV(RAND_CONV(RAND_CONV(RAND_CONV
                   (K(SYM ln)))))))) (REWRITE_RULE[READ_COMPONENT_COMPOSE] blo |>
                   fun _ -> blo) in
       let bob = daw_find_fact (fun c -> c = subst [s',`s:armstate`]
                  `read (memory :> bytelist(out,LENGTH(ob:byte list))) s = ob`) asl in
       ASSUME_TAC(MATCH_MP DAW_BYTELIST_APPEND (CONJ bob blo)))))),5;;

(* After a literal of len bytes from t (at ipv1): the decoding and the      *)
(* bytes of the stream after it (the model fact gives the condition).       *)
let DAW_AFTER_LIT_TAC (ipv1:term) (tl:term) (k:term) : tactic =
  fun (asl,w) ->
    let s = rand w in
    let mth = daw_model_fact asl in
    let cnd,(yes,_) = dest_cond(rhs(concl mth)) in
    let cth = TAC_PROOF((asl,cnd),REPEAT CONJ_TAC THEN DAW_ARITH_TAC) in
    let dth = TRANS (ASSUME `snappy_decode_tags m inp [] = snappy_decode_tags m rest ob`)
                    (REWRITE_RULE[cth] mth) in
    (* the bytes of the stream after the tag *)
    let r' = rand(rator yes) in
    let tb = daw_find_fact (fun c -> c = subst [ipv1,`a:int64`; tl,`t:byte list`; s,`s:armstate`]
               `read (memory :> bytelist(a,LENGTH(t:byte list))) s = t`) asl in
    let kle = TAC_PROOF((asl,mk_binary "<=" (k,mk_comb(`LENGTH:byte list->num`,tl))),DAW_ARITH_TAC) in
    let sfx = MATCH_MP READ_BYTELIST_SUFFIX (CONJ tb kle) in
    let eq = ISPECL [tl; k] SNAPPY_LENGTH_SUB_LIST_SUFFIX in
    let sfx = CONV_RULE(LAND_CONV(RATOR_CONV(RAND_CONV(RAND_CONV(RAND_CONV(RAND_CONV
                (K(SYM eq)))))))) sfx in
    let o' = rand yes in
    let lo = TAC_PROOF((asl,mk_eq(mk_comb(`LENGTH:byte list->num`,o'),
               `LENGTH(ob:byte list) + len`)),
               REWRITE_TAC[LENGTH_APPEND; LENGTH_SUB_LIST] THEN DAW_ARITH_TAC) in
    let lr = ISPECL [tl; k] SNAPPY_LENGTH_SUB_LIST_SUFFIX in
    let _ = r' in
    let lm = TAC_PROOF((asl,mk_binary "<=" (mk_comb(`LENGTH:byte list->num`,o'),`m:num`)),
               REWRITE_TAC[lo] THEN DAW_ARITH_TAC) in
    MAP_EVERY ASSUME_TAC [dth; sfx; lo; lr; lm] (asl,w);;

(* The 16-byte copy of TryFastAppend (ldp/stp): ghosts for the two 64-bit  *)
(* words at ip + 1 before, the bytes of the output and the facts after.     *)
let daw_pc_fast_ldp = `word(pc + 26140):int64` and daw_pc_fast_after = `word(pc + 26148):int64`;;

(* memrange(a,k) SUBSET the region of its base (input, output, d).        *)
let DAW_IN_REGION_TAC (a:term) (k:term) : tactic = fun (asl,w) ->
  let eq = DAW_ADDR_CONV a in
  let a' = rhs(concl eq) in
  let th = tryfind (fun (b,n) ->
      let t = daw_offset_from b a' in
      let le = mk_binary "<=" (mk_binop `(+):num->num->num` t k,n) in
      let lth = TAC_PROOF((asl,le),DAW_ARITH_TAC) in
      let th = MP (ISPECL [b;n;t;k] DAW_MEMRANGE_SUB) lth in
      let ad = lhand(rand(lhand(concl th))) in
      let eq2 = TRANS eq (SYM(DAW_ADDR_CONV ad)) in
      CONV_RULE(LAND_CONV(RAND_CONV(LAND_CONV(K(SYM eq2))))) th) daw_bases in
  ASSUME_TAC th (asl,w);;

let DAW_FAST_BEFORE_TAC (ipv:term) (ipv1:term) : tactic =
  (fun g -> if !daw_debug then print_endline "FASTHOOK"; ALL_TAC g) THEN
  DAW_IN_REGION_TAC ipv1 `8` THEN
  DAW_IN_REGION_TAC (daw_canon(mk_binop `word_add:int64->int64->int64` ipv1 `word 8:int64`)) `8` THEN
  DAW_OUT_REGION_TAC `LENGTH(ob:byte list)` `16` ipv `LENGTH(ob:byte list)` THEN
  DAW_OUT_REGION_TAC `LENGTH(ob:byte list) + 8` `8` ipv `LENGTH(ob:byte list)` THEN
  (fun (asl,w) -> if !daw_debug then List.iter (fun (_,th) -> if is_binary "SUBSET" (concl th) then
       print_endline ("  SUB " ^ string_of_term(concl th))) asl; ALL_TAC (asl,w)) THEN
  DAW_STATE_TAC (fun s ->
    let a2 = daw_canon(mk_binop `word_add:int64->int64->int64` ipv1 `word 8:int64`) in
    X_CHOOSE_THEN `g1:int64` ASSUME_TAC
      (prove(mk_exists(`g1:int64`,mk_eq(subst [ipv1,`a:int64`; s,`s:armstate`]
         `read (memory :> bytes64 a) s`,`g1:int64`)),MESON_TAC[])) THEN
    X_CHOOSE_THEN `g2:int64` ASSUME_TAC
      (prove(mk_exists(`g2:int64`,mk_eq(subst [a2,`a:int64`; s,`s:armstate`]
         `read (memory :> bytes64 a) s`,`g2:int64`)),MESON_TAC[])));;

let DAW_FAST_AFTER_TAC (ipv:term) (ipv1:term) : tactic =
  DAW_STATE_TAC (fun s -> W(fun (asl,w) ->
    let lob = `LENGTH(ob:byte list)` in
    let op = mk_binop `word_add:int64->int64->int64` `out:int64` (mk_comb(`word:num->int64`,lob)) in
    let b64 = function
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
             Comb(Comb(Const(":>",_),Const("memory",_)),Comb(Const("bytes64",_),a))),s1)),v)
          when s1 = s -> Some(a,v)
      | _ -> None in
    let facts = mapfilter (fun (_,th) -> match b64(concl th) with
        Some(a,v) -> (a,v,th) | None -> fail()) asl in
    (* the fact at address a (up to arithmetic), and another with its value *)
    let at a = tryfind (fun (b,v,th) ->
        let eq = daw_addr_eq asl b a in
        v, (if b = a then th else SUBS[eq] th)) facts in
    let src_of a v = tryfind (fun (b,v',th) ->
        if v' = v && (try ignore(daw_addr_eq asl b op); false with Failure _ -> true) &&
           (try ignore(daw_addr_eq asl b (mk_binop `word_add:int64->int64->int64` op `word 8:int64`)); false
            with Failure _ -> true)
        then let eq = daw_addr_eq asl b a in (if b = a then th else SUBS[eq] th)
        else fail()) facts in
    let op8 = mk_binop `word_add:int64->int64->int64` op `word 8:int64` in
    let ip8 = mk_binop `word_add:int64->int64->int64` ipv1 `word 8:int64` in
    let dump () = String.concat "; " (map (fun (a,v,_) -> string_of_term a ^ " -> " ^ string_of_term v) facts) in
    let at a = try at a with Failure _ -> failwith ("FAST: no store at " ^ string_of_term a ^ " among " ^ dump()) in
    let src_of a v = try src_of a v with Failure _ -> failwith ("FAST: no load at " ^ string_of_term a ^ " among " ^ dump()) in
    let v1,f1 = at op and v2,f2 = at op8 in
    let e1 = TRANS f1 (SYM(src_of ipv1 v1)) in
    let e2 = TRANS f2 (SYM(src_of ip8 v2)) in
    let pth = MATCH_MP READ_BYTELIST_OF_BYTES64_PAIR (CONJ e1 e2) in
    let tb = daw_find_fact (fun c -> c = subst [ipv1,`a:int64`; s,`s:armstate`]
               `read (memory :> bytelist(a,LENGTH(TL(rest:byte list)))) s = TL rest`) asl in
    let l16 = TAC_PROOF((asl,`0 + 16 <= LENGTH(TL(rest:byte list))`),DAW_ARITH_TAC) in
    let t16 = REWRITE_RULE[WORD_ADD_0; tb] (MP (ISPECL [`memory:(armstate,int64->byte)component`;
                ipv1; `0`; `16`; `LENGTH(TL(rest:byte list))`; s] READ_BYTELIST_SUB_LIST) l16) in
    let o16 = TRANS pth t16 in
    let ll = TAC_PROOF((asl,`0 + len <= 16`),DAW_ARITH_TAC) in
    let olen = REWRITE_RULE[WORD_ADD_0; o16] (MP (ISPECL [`memory:(armstate,int64->byte)component`;
                op; `0`; `len:num`; `16`; s] READ_BYTELIST_SUB_LIST) ll) in
    let olen = REWRITE_RULE[MP (ISPECL [`TL(rest:byte list)`; `len:num`; `16`] DAW_SUB_LIST_PREFIX_PREFIX)
                 (MP (ARITH_RULE `0 + len <= 16 ==> len <= 16`) ll)] olen in
    let ln = TAC_PROOF((asl,`LENGTH(SUB_LIST(0,len) (TL(rest:byte list))) = len`),
               REWRITE_TAC[LENGTH_SUB_LIST] THEN DAW_ARITH_TAC) in
    let bob = daw_find_fact (fun c -> c = subst [s,`s:armstate`]
                `read (memory :> bytelist(out,LENGTH(ob:byte list))) s = ob`) asl in
    let olen = CONV_RULE(LAND_CONV(RATOR_CONV(RAND_CONV(RAND_CONV(RAND_CONV(RAND_CONV
                 (K(SYM ln)))))))) olen in
    ASSUME_TAC(MATCH_MP DAW_BYTELIST_APPEND (CONJ bob olen)) THEN
    DAW_AFTER_LIT_TAC ipv1 `TL(rest:byte list)` `len:num`));;

let DAW_T_LIT_TAC (buf:bool) : tactic =
  let ipv = if buf then `word_add q (word i):int64` else `word_add d (word 41):int64` in
  let ipv1 = if buf then `word_add q (word (i + 1)):int64` else `word_add d (word 42):int64` in
  let kf = `val(HD(rest:byte list)) MOD 4 = 0` and lf = `val(HD(rest:byte list)) DIV 4 < 60` in
  let nilf = `~(rest:byte list = [])` in
  DAW_T_PREP_TAC buf [] THEN
  ASSUME_TAC(SPEC `HD(rest:byte list)` DAW_TAG_BOUNDS) THEN
  (let mth = MP (SPECL [`m:num`; `HD(rest:byte list)`; `TL(rest:byte list)`; `ob:byte list`]
                       DAW_DECODE_LITERAL) (CONJ (ASSUME kf) (ASSUME lf)) in
   let mth = CONV_RULE(TOP_DEPTH_CONV let_CONV)
               (REWRITE_RULE[SYM(MATCH_MP CONS_HD_TL (ASSUME nilf))] mth) in
   ASSUME_TAC mth) THEN
  SUBGOAL_THEN `val(HD(rest:byte list)) DIV 4 + 1 < 2 EXP 32`
    (fun th -> ASSUME_TAC(MATCH_MP DAW_WORD_ADD_ZX1 th)) THENL
   [DAW_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `len = val(HD(rest:byte list)) DIV 4 + 1` THEN
  SUBGOAL_THEN `len < 2 EXP 32` (fun th -> ASSUME_TAC(MATCH_MP DAW_ZX64_WORD th)) THENL
   [DAW_ARITH_TAC; ALL_TAC] THEN
  (* ip_limit_ - (ip + 1) and op_limit_ - op as words of numbers *)
  SUBGOAL_THEN (subst [ipv,`x:int64`]
    `word_sub (word_add (x:int64) (word(LENGTH(rest:byte list)))) (word_add x (word 1)) =
     word(LENGTH(TL rest))`) ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(ASSUME `LENGTH(TL(rest:byte list)) + 1 = LENGTH rest`)] THEN
    REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN (subst [ipv,`x:int64`; ipv1,`y:int64`]
    `word_sub (word_add (x:int64) (word(LENGTH(rest:byte list)))) y =
     word(LENGTH(TL rest))`) ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(ASSUME `LENGTH(TL(rest:byte list)) + 1 = LENGTH rest`)] THEN
    REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word_add out (word m)) (word_add out (word(LENGTH(ob:byte list)))):int64 =
                word(m - LENGTH ob)` ASSUME_TAC THENL
   [MATCH_MP_TAC DAW_WORD_SUB_ADD_LE THEN DAW_ARITH_TAC; ALL_TAC] THEN
  W(fun (asl,w) ->
    let codes = mapfilter (fun (_,th) ->
        let c = concl th in
        if can (term_match [] `word_zx (x:int32):int64 = word n`) c ||
           can (term_match [] `word_zx (x:int64):int32 = word n`) c ||
           can (term_match [] `word_sub (word_add x (word a)) (word_add x (word b)):int64 = word n`) c ||
           can (term_match [] `word_sub (word_add x (word a)) (word_add y (word b)):int64 = word n`) c
        then th else fail()) asl in
    if !daw_debug then List.iter (fun th -> Printf.printf "LITCODE %s\n%!" (string_of_thm th)) codes;
    DAW_RUN_FROM_TAC ~rws:(daw_rws @ [daw_and3_rw 0; SPEC `HD(rest:byte list)` DAW_TAG_USHR2;
                                       WORD_ADD_0] @ codes)
      ~norm:(DAW_PC_HOOK_TAC [daw_pc_fast_ldp, DAW_FAST_BEFORE_TAC ipv ipv1;
                              daw_pc_fast_after, DAW_FAST_AFTER_TAC ipv ipv1])
      ~calls:[daw_pc_memcpy, (fun i -> let tac,u = DAW_MEMCPY_LIT_TAC ipv i in
                                (tac THEN TRY(DAW_AFTER_LIT_TAC ipv1 `TL(rest:byte list)` `len:num`)),u);
              daw_pc_refill, DAW_REFILL_CALL_TAC buf]
      daw_exec DAW_LEAF_TAC);;

(* Long literals: the tag byte v = 240, 244, 248, 252 with k = 1..4 length *)
(* bytes.                                                                    *)
let DAW_T_LONG_TAC (buf:bool) (v:int) : tactic =
  let k = v / 4 - 59 in
  let kt = mk_small_numeral k and vt = mk_small_numeral v in
  let ipv = if buf then `word_add q (word i):int64` else `word_add d (word 41):int64` in
  let ipv1 = if buf then `word_add q (word (i + 1)):int64` else `word_add d (word 42):int64` in
  let vf = subst [vt,`v:num`] `val(HD(rest:byte list)) = v` in
  let nilf = `~(rest:byte list = [])` in
  let kle = subst [kt,`k:num`] `k <= LENGTH(TL(rest:byte list))` in
  let tl = `TL(rest:byte list)` in
  SUBGOAL_THEN (subst [kt,`k:num`] `k + 1 <= LENGTH(rest:byte list)`) ASSUME_TAC THENL
   [(if buf then DAW_ARITH_TAC else
     MP_TAC(MATCH_MP DAW_TAG_NEEDED (ASSUME `snappy_refill_ok(rest:byte list)`)) THEN
     ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC); ALL_TAC] THEN
  DAW_T_PREP_TAC buf [k] THEN
  ASSUME_TAC(CONV_RULE NUM_REDUCE_CONV (MP (SPECL [tl; kt]
     DAW_NUM_OF_BYTELIST_SUB_BOUND) (ASSUME kle))) THEN
  (let hyp = `val(HD(rest:byte list)) MOD 4 = 0 /\ ~(val(HD rest) DIV 4 < 60) /\
              val(HD rest) DIV 4 - 59 <= LENGTH(TL rest)` in
   let hth = EQT_ELIM((REWRITE_CONV[ASSUME vf] THENC NUM_REDUCE_CONV THENC
                       REWRITE_CONV[ASSUME kle]) hyp) in
   let mth = MP (SPECL [`m:num`; `HD(rest:byte list)`; tl; `ob:byte list`]
                       DAW_DECODE_LONG_LITERAL) hth in
   let mth = CONV_RULE(TOP_DEPTH_CONV let_CONV)
               (REWRITE_RULE[SYM(MATCH_MP CONS_HD_TL (ASSUME nilf))] mth) in
   let mth = CONV_RULE(RAND_CONV(REWRITE_CONV[ASSUME vf] THENC NUM_REDUCE_CONV)) mth in
   ASSUME_TAC mth) THEN
  (* the bytes of the literal after the length bytes *)
  DAW_STATE_TAC (fun s -> W(fun (asl,w) ->
    let tb = daw_find_fact (fun c -> c = subst [ipv1,`a:int64`; s,`s:armstate`]
               `read (memory :> bytelist(a,LENGTH(TL(rest:byte list)))) s = TL rest`) asl in
    let sfx = MATCH_MP READ_BYTELIST_SUFFIX (CONJ tb (ASSUME kle)) in
    let eq = ISPECL [tl; kt] SNAPPY_LENGTH_SUB_LIST_SUFFIX in
    let sfx = CONV_RULE(LAND_CONV(RATOR_CONV(RAND_CONV(RAND_CONV(RAND_CONV(RAND_CONV
                (K(SYM eq)))))))) sfx in
    let ad = DAW_ADDR_CONV (lhand(rand(rand(rand(rator(lhand(concl sfx))))))) in
    ASSUME_TAC(REWRITE_RULE[ad] sfx) THEN ASSUME_TAC eq)) THEN
  ASSUME_TAC(CONV_RULE(RAND_CONV(RAND_CONV NUM_REDUCE_CONV))
    (REWRITE_RULE[ASSUME vf] (SPEC `HD(rest:byte list)` DAW_TAG_USHR2))) THEN
  SUBGOAL_THEN (subst [kt,`k:num`] `num_of_bytelist(SUB_LIST(0,k) (TL(rest:byte list))) < 2 EXP 32`)
    (fun th -> ASSUME_TAC(MATCH_MP DAW_ADD_ZX32_1 th)) THENL
   [DAW_ARITH_TAC; ALL_TAC] THEN
  ASSUME_TAC(SYM(SPECL [subst [kt,`k:num`] `num_of_bytelist(SUB_LIST(0,k) (TL(rest:byte list)))`;
                         `1`] (INST_TYPE [`:64`,`:N`] WORD_ADD))) THEN
  ABBREV_TAC (subst [kt,`k:num`] `len = num_of_bytelist(SUB_LIST(0,k) (TL(rest:byte list))) + 1`) THEN
  W(fun (asl,w) ->
    let codes = mapfilter (fun (_,th) ->
        let c = concl th in
        if can (term_match [] `word_and (b:int32) (word k) = word n`) c ||
           can (term_match [] `word_add (word_zx (word n:int32)) (word 1):int64 = word m`) c ||
           can (term_match [] `word_add (word n) (word 1):int64 = word m`) c ||
           can (term_match [] `word_ushr (word_zx (HD(rest:byte list)):int32) 2 = word n`) c
        then th else fail()) asl in
    let fixl = (* the memcpy result as SUB_LIST(k,len) t *)
      DAW_STATE_TAC (fun s' -> W(fun (asl,w) ->
        let le = TAC_PROOF((asl,mk_binary "<=" (mk_binop `(+):num->num->num` kt `len:num`,
                   mk_comb(`LENGTH:byte list->num`,tl))),DAW_ARITH_TAC) in
        let pth = MP (ISPECL [tl; kt; `len:num`] SNAPPY_SUFFIX_PREFIX) le in
        RULE_ASSUM_TAC(fun th -> match concl th with
            Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),s1)),_) when s1 = s' ->
              REWRITE_RULE[pth] th
          | _ -> th))) in
    DAW_RUN_FROM_TAC ~rws:(daw_rws @ [daw_and3_rw 0 |> CONV_RULE(RAND_CONV(REWRITE_CONV[ASSUME vf] THENC NUM_REDUCE_CONV)) ;
                                       WORD_ADD_0] @ codes)
      ~calls:[daw_pc_memcpy, (fun i -> let tac,u = DAW_MEMCPY_LIT_TAC ipv i in
                                (tac THEN TRY(fixl THEN DAW_AFTER_LIT_TAC ipv1 tl
                                   (mk_binop `(+):num->num->num` kt `len:num`))),u);
              daw_pc_refill, DAW_REFILL_CALL_TAC buf]
      daw_exec DAW_LEAF_TAC);;

(* ------------------------------------------------------------------------- *)
(* T by the class of the tag byte HD rest: the literal, the long literal by  *)
(* its byte (240, 244, 248, 252), the copies with 1-, 2- and 4-byte offsets. *)
(* A class is a conjunct of the precondition (daw_class_goal); each is a job *)
(* of its own in the link (..._t_{b,s}_<class>_{spec,proof}.ml), and        *)
(* DAW_T_FROM_CLASSES_TAC gives the segment from them.                       *)
(* ------------------------------------------------------------------------- *)

let daw_tag_classes =
  ["LIT"; "LONG240"; "LONG244"; "LONG248"; "LONG252"; "COPY1"; "COPY2"; "COPY4"];;

(* The facts of a class, in the order of the case split of the tag in        *)
(* DAW_T_CLASS_TAC (as the cases of ASM_CASES_TAC leave them).               *)
let daw_class_facts name =
  let m k = subst [mk_small_numeral k,`k:num`] `val(HD(rest:byte list)) MOD 4 = k` in
  let l = `val(HD(rest:byte list)) DIV 4 < 60` in
  match name with
    "LIT" -> [m 0; l]
  | "LONG240" | "LONG244" | "LONG248" | "LONG252" ->
      let v = int_of_string (String.sub name 4 3) in
      [m 0; mk_neg l;
       subst [mk_small_numeral v,`v:num`] `val(HD(rest:byte list)) = v`]
  | "COPY1" -> [mk_neg(m 0); m 1]
  | "COPY2" -> [mk_neg(m 0); mk_neg(m 1); m 2]
  | "COPY4" -> [mk_neg(m 0); mk_neg(m 1); mk_neg(m 2); m 3]
  | _ -> failwith ("daw_class_facts: " ^ name);;

let daw_class_cond name = list_mk_conj(daw_class_facts name);;

(* The segment from T (buf: the buffer, else scratch_) for one class.        *)
let daw_class_goal (buf:bool) name =
  let vs,body = strip_exists (if buf then daw_tb else daw_ts) in
  list_mk_forall(`n:num`::daw_vars,
    daw_seg (list_mk_exists(vs,mk_conj(body,daw_class_cond name))));;

(* The classes cover the tag bytes.                                          *)
let DAW_CLASS_SPLIT = prove
 (list_mk_disj(map daw_class_cond daw_tag_classes),
  MP_TAC(ISPEC `HD(rest:byte list)` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SPEC_TAC(`val(HD(rest:byte list))`,`v:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

(* The contradiction of a tag that needs more bytes than scratch_ holds.    *)
let DAW_T_SHORT_TAC (reduce:bool) : tactic =
  MP_TAC(MATCH_MP DAW_TAG_NEEDED (ASSUME `snappy_refill_ok(rest:byte list)`)) THEN
  ASM_REWRITE_TAC[] THEN (if reduce then CONV_TAC NUM_REDUCE_CONV else ALL_TAC) THEN
  DISCH_TAC THEN SUBGOAL_THEN `F` CONTR_TAC THEN DAW_ARITH_TAC;;

let DAW_T_CLASS_TAC (buf:bool) name : tactic =
  DAW_CUT_START_TAC buf THEN
  ASSUME_TAC(SPEC `HD(rest:byte list)` DAW_TAG_BOUNDS) THEN
  MAP_EVERY (fun t -> UNDISCH_THEN t ASSUME_TAC) (daw_class_facts name) THEN
  (match name with
     "LIT" -> DAW_T_LIT_TAC buf
   | "LONG252" when not buf -> DAW_T_SHORT_TAC true
   | "LONG240" | "LONG244" | "LONG248" | "LONG252" ->
       DAW_T_LONG_TAC buf (int_of_string (String.sub name 4 3))
   | "COPY1" -> DAW_T_COPY12_TAC buf 1
   | "COPY2" -> DAW_T_COPY12_TAC buf 2
   | "COPY4" -> if buf then DAW_T_COPY4_TAC else DAW_T_SHORT_TAC false
   | _ -> failwith ("DAW_T_CLASS_TAC: " ^ name));;

(* The segment from T from the theorems of its classes (daw_class_goal, in   *)
(* the order of daw_tag_classes): for the state and the witnesses of the     *)
(* precondition, the class of HD rest (DAW_CLASS_SPLIT) and its theorem.     *)
let DAW_T_FROM_CLASSES_TAC (ths:thm list) : tactic =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[ensures] THEN X_GEN_TAC `s:armstate` THEN
  DISCH_THEN(MP_TAC o BETA_RULE) THEN
  DISCH_THEN(X_CHOOSE_THEN `ipv:int64` (X_CHOOSE_THEN `rest:byte list`
    (X_CHOOSE_THEN `ob:byte list` (X_CHOOSE_THEN `i:num` ASSUME_TAC)))) THEN
  MP_TAC DAW_CLASS_SPLIT THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  W(fun (asl,w) ->
    let body = concl(snd(el 1 asl)) and cond = concl(snd(hd asl)) in
    let wit = CONJ (ASSUME body) (ASSUME cond) in
    let ok th =
      let th1 = MP (SPECL (`n:num`::daw_vars) th) (ASSUME daw_hyp) in
      let th2 = SPEC `s:armstate` (REWRITE_RULE[ensures] th1) in
      let bth = TRY_CONV BETA_CONV (lhand(concl th2)) in
      let ant' = rand(concl bth) in
      let vs,b = strip_exists ant' in
      if not(aconv b (concl wit)) then failwith "class" else
      let eth = itlist (fun v th -> EXISTS (mk_exists(v,concl th),v) th) vs wit in
      let eth = EQ_MP (SYM bth) (EQ_MP (ALPHA (concl eth) ant') eth) in
      MP th2 eth in
    let th = tryfind ok ths in
    ACCEPT_TAC th);;

