(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)
(* ========================================================================= *)
(* DecompressBranchless<char*> (0x6050), the fast loop of the array writer:  *)
(* the lemmas, the cut points and the tactics of the proof of correctness and *)
(* memory safety (decompress_branchless_spec.ml), and the statements of the  *)
(* leaves of the tag segment. The pattern-copy leaves (by offset) are proved *)
(* in three jobs of their own (decompress_branchless_near{1,2a,2b}_proof.ml), *)
(* the rest in decompress_branchless_proof.ml.                               *)
(*                                                                           *)
(* First assembled by a development script, now maintained by hand.        *)
(*                                                                           *)
(* Three kinds of cut point, with a measure (ENSURES_MEASURE_INDUCT):        *)
(*   TAG (0x6140 for the first tag of an iteration, w = 2; 0x61f0 for the   *)
(*       second, w = 1) for the tag at position h of the input,             *)
(*       measure 2 (L - h) + 1;                                             *)
(*   J   (0x61e4, after a tag, the limit checks), measure 2 (L - h) + 2;    *)
(*   E   (0x6238, the exit: flush of the deferred copy and return), 0.      *)
(* At each: the output so far ob at base (op = LENGTH ob), the deferred copy *)
(* db at dsrc (dl = LENGTH db <= 64), and the model                          *)
(*   snappy_steps k m (inp,out) = SOME(SUB_LIST(h,L - h) inp, APPEND ob db). *)
(* The flushes are MemCopy64 by its contract (DB_FLUSH); the tag segment is  *)
(* split into leaves by the class of the tag and, for copies with an offset *)
(* below the length (Copy64BytesWithPatternExtension), by the offset: the   *)
(* pattern copies for each offset 1..16 (TBL with the pattern masks), the    *)
(* chunk copy for offsets 17..63.                                            *)
(* ========================================================================= *)


needs "arm/proofs/snappy/gcc12_O2/decompress_branchless_spec.ml";;
needs "common/snappy/snappy_memory.ml";;
needs "common/ensures_measure.ml";;
needs "arm/proofs/snappy/bstep_decide.ml";;
needs "arm/proofs/snappy/gcc12_O2/length_minus_offset_lib.ml";;

(* ------------------------------------------------------------------------- *)
(* Words.                                                                    *)
(* ------------------------------------------------------------------------- *)

let DB_VAL_WORD_ZX_BYTE = prove
 (`!c:byte. val(word_zx c:int64) = val c`,
  GEN_TAC THEN MATCH_MP_TAC VAL_WORD_ZX THEN
  REWRITE_TAC[DIMINDEX_8; DIMINDEX_64] THEN ARITH_TAC);;

let DB_AND3 = prove
 (`!c:byte. word_and (word_zx c) (word 3):int64 = word(val c MOD 4)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`word_zx (c:byte):int64`; `2`] (CONJUNCT1 WORD_AND_MASK_WORD)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[DB_VAL_WORD_ZX_BYTE]);;

let DB_USHR2 = prove
 (`!c:byte. word_ushr (word_zx c) 2:int64 = word(val c DIV 4)`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM WORD_VAL] THEN
  REWRITE_TAC[VAL_WORD_USHR; DB_VAL_WORD_ZX_BYTE] THEN CONV_TAC NUM_REDUCE_CONV);;

(* The offset bits ExtractOffset keeps of the 16 bits after the tag, by type *)
(* (the 64-bit and the 32-bit and of the code).                              *)

let DB_AND16_T0 = prove
 (`(!x:int16. word_and (word_zx x) (word 16711680):int32 = word 0) /\
   (!x:int16. word_and (word_zx x) (word 16711680):int64 = word 0)`,
  CONJ_TAC THEN BITBLAST_TAC);;

let DB_AND16_T1 = prove
 (`(!x:int16. word_and (word_zx x) (word 4294902015):int32 = word_zx(word_zx x:byte)) /\
   (!x:int16. word_and (word_zx x) (word 4294902015):int64 = word_zx(word_zx x:byte))`,
  CONJ_TAC THEN BITBLAST_TAC);;

let DB_AND16_T2 = prove
 (`(!x:int16. word_and (word_zx x) (word 65535):int32 = word_zx x) /\
   (!x:int16. word_and (word_zx x) (word 65535):int64 = word_zx x)`,
  CONJ_TAC THEN BITBLAST_TAC);;

let DB_SX_IWORD_SUB = prove
 (`!a b. a < 32768 /\ b <= 32768
         ==> word_sx(iword(&a - &b):int16):int64 = word_sub (word a) (word b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_sx] THEN
  SUBGOAL_THEN `ival(iword(&a - &b):int16) = &a - &b` SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_16] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_LE]) THEN
    ASM_INT_ARITH_TAC;
    REWRITE_TAC[IWORD_INT_SUB; GSYM WORD_IWORD]]);;

let DB_SX_IWORD_NUM = prove
 (`!a. a < 32768 ==> word_sx(iword(&a):int16):int64 = word a`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`a:num`; `0`] DB_SX_IWORD_SUB) THEN
  ASM_REWRITE_TAC[INT_SUB_RZERO; LE_0; WORD_SUB_0]);;

let DB_WORD_256 = prove
 (`!k. word(256 * k):int64 = word_shl (word k) 8`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_SHL; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV MOD_DOWN_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MULT_SYM]);;

(* Stated here (assuming_proofs, common/relative.ml), proved in the job      *)
(* decompress_branchless_lemmas_proof.ml.                                    *)
let DB_AND255_X_STMT =
 `!x y:int64. val x < 256 ==> word_and (word_sub x (word_shl y 8)) (word 255) = x`;;

let DB_AND255_X = assuming_proofs (fun () -> prove(DB_AND255_X_STMT, BITBLAST_TAC));;

let DB_AND255_SUB = prove
 (`!a k. a < 256
         ==> word_and (word_sub (word a) (word (256 * k))) (word 255):int64 =
             word a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DB_WORD_256] THEN
  MATCH_MP_TAC DB_AND255_X THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `a < 256 ==> a < 2 EXP 64`]);;

(* ------------------------------------------------------------------------- *)
(* Regions at offsets from a base.                                           *)
(* ------------------------------------------------------------------------- *)

let DB_NONOVERLAPPING_OFFSETS = prove
 (`!(a:int64) x k y l. x + k <= y /\ y + l <= 2 EXP 64
     ==> nonoverlapping (word_add a (word x),k) (word_add a (word y),l)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_MEMRANGE; DISJOINT; EXTENSION; IN_INTER; IN_MEMRANGE; NOT_IN_EMPTY] THEN
  X_GEN_TAC `z:int64` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `z = word_add (word_add a (word x)) (word i):int64` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; WORD_RULE `word_add a x = word_add a y <=> x = y`] THEN
  REWRITE_TAC[WORD_EQ; DIMINDEX_64; CONG] THEN
  SUBGOAL_THEN `(x + i) MOD 2 EXP 64 = x + i /\ (y + j) MOD 2 EXP 64 = y + j` (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;
let DB_NONOVERLAPPING_OFFSETS0 = prove
 (`!(a:int64) k y l. k <= y /\ y + l <= 2 EXP 64
     ==> nonoverlapping (a,k) (word_add a (word y),l)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`a:int64`; `0`; `k:num`; `y:num`; `l:num`] DB_NONOVERLAPPING_OFFSETS) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; WORD_ADD_0]);;
let DB_SUBSET_OFFSETS = prove
 (`!(base:int64) x k y l.
        y <= x /\ x + k <= y + l
        ==> memrange(word_add base (word x),k) SUBSET
            memrange(word_add base (word y),l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_MEMRANGE] THEN
  X_GEN_TAC `a:int64` THEN DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(x - y) + i` THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `x = y + (x - y)` (fun th ->
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV o RAND_CONV) [th]) THENL
   [ASM_ARITH_TAC; REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE]);;
let DB_SUBSET_OFFSETS0 = prove
 (`!(base:int64) x k l.
        x + k <= l
        ==> memrange(word_add base (word x),k) SUBSET memrange(base,l)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`base:int64`; `x:num`; `k:num`; `0`; `l:num`] DB_SUBSET_OFFSETS) THEN
  ASM_REWRITE_TAC[LE_0; ADD_CLAUSES; WORD_ADD_0]);;
let DB_NONOVERLAPPING_SUB = prove
 (`!(base:int64) m x k b l.
     nonoverlapping (base,m) (b,l) /\ x + k <= m
     ==> nonoverlapping (word_add base (word x),k) (b,l)`,
  REWRITE_TAC[NONOVERLAPPING_MEMRANGE] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`base:int64`; `x:num`; `k:num`; `m:num`] DB_SUBSET_OFFSETS0) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;
let DB_BYTELIST_OF_BYTES = prove
 (`!(m:(S,N word->byte)component) a b k s t.
     read (m :> bytes(a,k)) s = read (m :> bytes(b,k)) t
     ==> read (m :> bytelist(a,k)) s = read (m :> bytelist(b,k)) t`,
  REWRITE_TAC[bytelist; READ_COMPONENT_COMPOSE; through; read] THEN SIMP_TAC[]);;
let DB_SUBSUMED_APPLY = prove
 (`!(R:A->A->bool) R' s s'. R subsumed R' /\ R s s' ==> R' s s'`,
  REWRITE_TAC[subsumed] THEN MESON_TAC[]);;
(* F subsumed C, for F a chain whose last clauses are byte regions inside the last clause of C *)
let rec db_frame_subsumed asl (sub_tac:tactic) (f:term) (c:term) : thm =
  if f = c then ISPEC f SUBSUMED_REFL else
  match f,c with
    Comb(Comb(Const(",,",_),x),y),Comb(Comb(Const(",,",_),x'),y') when x = x' ->
      MATCH_MP SUBSUMED_SEQ (CONJ (ISPEC x SUBSUMED_REFL) (db_frame_subsumed asl sub_tac y y'))
  | Comb(Comb(Const(",,",_),x),y),_ ->
      let thx = db_frame_subsumed asl sub_tac x c and thy = db_frame_subsumed asl sub_tac y c in
      let th = MATCH_MP SUBSUMED_SEQ (CONJ thx thy) in
      let idem = prove(mk_eq(list_mk_icomb ",," [c;c],c), MAYCHANGE_IDEMPOT_TAC) in
      REWRITE_RULE[idem] th
  | Comb(Const("MAYCHANGE",_),Comb(Comb(Const("CONS",_),Comb(Comb(Const(":>",_),_),Comb(Const("bytes",_),r))),_)),
    Comb(Const("MAYCHANGE",_),Comb(Comb(Const("CONS",_),Comb(Comb(Const(":>",_),_),Comb(Const("bytes",_),r'))),_)) ->
      let st = mk_icomb(mk_icomb(`(SUBSET):(int64->bool)->(int64->bool)->bool`, mk_icomb(`memrange:int64#num->int64->bool`,r)), mk_icomb(`memrange:int64#num->int64->bool`,r')) in
      let sth = TAC_PROOF((asl,st),sub_tac) in
      MATCH_MP (ISPEC `memory:(armstate,int64->byte)component` MAYCHANGE_BYTES_SUBSUMED) sth
  | _ -> failwith ("db_frame_subsumed: " ^ string_of_term f);;
let DB_SUBSET_PREFIX = prove
 (`!(a:int64) k l. k <= l ==> memrange(a,k) SUBSET memrange(a,l)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`a:int64`; `0`; `k:num`; `l:num`] DB_SUBSET_OFFSETS0) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; WORD_ADD_0]);;

let db_exec = SNAPPY_DECOMPRESS_BRANCHLESS_CHARP_GCC12_O2_EXEC;;


(* ------------------------------------------------------------------------- *)
(* Statements of the states at the cut points.                               *)
(* ------------------------------------------------------------------------- *)

(* Statements of the cut-point lemmas (strings, parsed). *)
let db_fp = "word_sub sp (word 240)";;
let db_slot k = if k = 0 then "read (memory :> bytes64 (word_sub sp (word 240))) s"
  else Printf.sprintf "read (memory :> bytes64 (word_add (word_sub sp (word 240)) (word %d))) s" k;;
let db_frame_facts =
  String.concat " /\\\n" (map (fun (k,v) -> db_slot k ^ " = " ^ v)
   [0,"x29"; 8,"returnaddress"; 16,"x19"; 24,"x20"; 32,"x21"; 40,"x22";
    48,"x23"; 56,"x24"; 64,"x25"; 72,"x26"; 80,"x27"; 88,"x28";
    104,"word_add (word pc) (word 32256)";
    112,"word_add (word_sub sp (word 240)) (word 176)";
    120,"word_sub (word_add ip (word li)) (word 129)";
    160,"dsrc"; 168,"word dl"]);;
let db_rd = "(memrange(ip:int64,li) UNION memrange(base,m) UNION memrange(word_sub sp (word 288),288) UNION memrange(word pc,32789) UNION memrange(word(pc + 129968),1120) UNION memrange(ea,el))";;
let db_wr = "(memrange(base,m) UNION memrange(word_sub sp (word 288),288))";;
let db_common =
 "aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\\
  read SP s = word_sub sp (word 240) /\\
  read X29 s = word_sub sp (word 240) /\\
  read X20 s = base /\\
  read X21 s = word_sub (word lim) (word 64) /\\
  read X23 s = word_add (word_sub sp (word 240)) (word 160) /\\
  read X24 s = word_add (word_sub sp (word 240)) (word 168) /\\
  read X28 s = word op /\\
  read (memory :> bytelist(ip,li)) s = inp /\\
  read (memory :> bytelist(base,op)) s = ob /\\
  read (memory :> bytelist(dsrc,dl)) s = db /\\
  read (memory :> bytes(word(pc + 129968),1120)) s = rw /\\
  read (memory :> bytes(ea,el)) s = ev /\\\n" ^ db_frame_facts ^ " /\\
  (?e2. read events s = APPEND e2 e /\\ memaccess_inset e2 " ^ db_rd ^ " " ^ db_wr ^ ")";;
let db_static =
 "snappy_steps k m (inp,out) = SOME(SUB_LIST(h,li - h) inp,APPEND ob db) /\\
  LENGTH ob = op /\\ LENGTH db = dl /\\ dl <= 64 /\\
  nonoverlapping (word_add (base:int64) (word op),dl) (dsrc:int64,dl) /\\
  nonoverlapping (dsrc,dl) (word_sub (sp:int64) (word 288),288) /\\
  memrange(dsrc,64) SUBSET " ^ db_rd;;
let db_tag_bounds = "h + 70 <= li /\\ op + dl < lim /\\ (w = 2 ==> h + 130 < li /\\ op + dl + 64 < lim) /\\ 1 <= w /\\ w <= 2";;
let db_j_bounds = "h + 9 <= li /\\ (0 < dl ==> op + 64 <= m) /\\ (w = 2 ==> h + 70 <= li /\\ op + dl < lim) /\\ 1 <= w /\\ w <= 2";;
let db_e_bounds = "h <= li /\\ (0 < dl ==> op + 64 <= m)";;
let db_tag_pre =
 "read PC s = word(pc + (if w = 2 then 24896 else 25072)) /\\
  read X19 s = word_add ip (word (h + 1)) /\\
  read X27 s = word_zx (EL h inp) /\\
  read X8 s = word dl /\\ " ^ db_common;;
let db_j_pre =
 "read PC s = word(pc + 25060) /\\
  read X19 s = word_add ip (word (h + 1)) /\\
  read X27 s = word_zx (EL h inp) /\\
  read X26 s = word w /\\ " ^ db_common;;
let db_e_pre =
 "read PC s = word(pc + 25144) /\\
  read X22 s = word_add ip (word (h + 1)) /\\
  read X8 s = word dl /\\ " ^ db_common;;
let db_ghosts = "h op dl dsrc ob db k";;
let db_R =
 "\\n s. (?" ^ db_ghosts ^ " w. n = 2 * (li - h) + 1 /\\ (" ^ db_static ^ ") /\\ (" ^ db_tag_bounds ^ ") /\\ (" ^ db_tag_pre ^ ")) \\/
        (?" ^ db_ghosts ^ " w. n = 2 * (li - h) + 2 /\\ (" ^ db_static ^ ") /\\ (" ^ db_j_bounds ^ ") /\\ (" ^ db_j_pre ^ ")) \\/
        (n = 0 /\\ ?" ^ db_ghosts ^ ". (" ^ db_static ^ ") /\\ (" ^ db_e_bounds ^ ") /\\ (" ^ db_e_pre ^ "))";;
let db_Q =
 "\\s. read PC s = returnaddress /\\ read SP s = sp /\\
      read X19 s = x19 /\\ read X20 s = x20 /\\ read X21 s = x21 /\\
      read X22 s = x22 /\\ read X23 s = x23 /\\ read X24 s = x24 /\\
      read X25 s = x25 /\\ read X26 s = x26 /\\ read X27 s = x27 /\\
      read X28 s = x28 /\\ read X29 s = x29 /\\
      (?k inp' out'.
         snappy_steps k m (inp,out) = SOME(inp',out') /\\
         read X0 s = word_add ip (word(LENGTH inp - LENGTH inp')) /\\
         read X1 s = word(LENGTH out') /\\
         read (memory :> bytelist(base,LENGTH out')) s = out') /\\
      ?e2. read events s = APPEND e2 e /\\
           memaccess_inset e2
            (memrange(ip,LENGTH inp) UNION memrange(base,m) UNION
             memrange(word_sub sp (word 288),288) UNION
             memrange(word pc,libsnappy_size) UNION
             memrange(word(pc + libsnappy_rw),libsnappy_rw_size) UNION
             memrange(ea,el))
            (memrange(base,m) UNION memrange(word_sub sp (word 288),288))";;
let db_C =
 "MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
  MAYCHANGE [SP; X18; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
  MAYCHANGE [memory :> bytes(word_sub sp (word 240),240)] ,,
  MAYCHANGE [memory :> bytes(word_sub sp (word 288),48)] ,,
  MAYCHANGE [memory :> bytes(base,m)]";;
let db_G =
 "memmove_correct_safe_contract (imp \"memmove\") ea el ev /\\
  aligned 4096 (word pc:int64) /\\
  pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\\
  elf_relocated_data (word(pc + libsnappy_rw)) rw (snappy_libsnappy_gcc12_O2_relocated pc imp) /\\
  aligned 16 sp /\\ LENGTH (inp:byte list) = li /\\
  val ip + li < 2 EXP 64 /\\ LENGTH (out:byte list) <= m /\\ m < 2 EXP 32 /\\ val base + m < 2 EXP 64 /\\
  lim + 63 = m /\\ li < 2 EXP 63 /\\ 130 < li /\\ 64 < lim /\\
  nonoverlapping (base,m) (word pc,libsnappy_rw + libsnappy_rw_size) /\\
  nonoverlapping (base,m) (ea,el) /\\
  nonoverlapping (word_sub sp (word 288),288) (word pc,libsnappy_rw + libsnappy_rw_size) /\\
  nonoverlapping (word_sub sp (word 288),288) (ea,el) /\\
  nonoverlapping (base,m) (word_sub sp (word 288),288) /\\
  nonoverlapping (ip,li) (base,m) /\\
  nonoverlapping (ip,li) (word_sub sp (word 288),288)";;
let db_allvars = "e ip inp li base out m lim pc rw sp returnaddress x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 ea el ev";;
let db_lemma pre bounds measure =
  parse_term ("!" ^ db_allvars ^ " " ^ db_ghosts ^ " w. (" ^ db_G ^ ") /\\ (" ^ db_static ^ ") /\\ (" ^ bounds ^ ")
    ==> ensures arm (\\s. " ^ pre ^ ") (\\s. (" ^ db_Q ^ ") s \\/ ?n'. n' < " ^ measure ^ " /\\ (" ^ db_R ^ ") n' s) (" ^ db_C ^ ")");;
let DB_TAG_STMT = db_lemma db_tag_pre db_tag_bounds "2 * (li - h) + 1";;

(* ------------------------------------------------------------------------- *)
(* Signed compares as integers, branch decisions.                            *)
(* ------------------------------------------------------------------------- *)

let DB_IVAL_WORD_NUM = prove
 (`!n. n < 2 EXP 63 ==> ival(word n:int64) = &n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word n:int64) = n` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `word n:int64` IVAL_EQ_VAL) THEN
  ASM_REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let DB_IVAL_WORD_ADD = prove
 (`!x y:int64. --(&2 pow 63) <= ival x + ival y /\ ival x + ival y < &2 pow 63
               ==> ival(word_add x y) = ival x + ival y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_add x y:int64 = iword(ival x + ival y)` SUBST1_TAC THENL
   [REWRITE_TAC[IWORD_INT_ADD; IWORD_IVAL]; ALL_TAC] THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let DB_IVAL_WORD_SUB = prove
 (`!x y:int64. --(&2 pow 63) <= ival x - ival y /\ ival x - ival y < &2 pow 63
               ==> ival(word_sub x y) = ival x - ival y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_sub x y:int64 = iword(ival x - ival y)` SUBST1_TAC THENL
   [REWRITE_TAC[IWORD_INT_SUB; IWORD_IVAL]; ALL_TAC] THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let DB_IVAL_WORD_ZX = prove
 (`(!b:byte. ival(word_zx b:int64) = &(val b)) /\
   (!b:int16. ival(word_zx b:int64) = &(val b)) /\
   (!b:int32. ival(word_zx b:int64) = &(val b))`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC[word_zx] THEN
  MATCH_MP_TAC DB_IVAL_WORD_NUM THEN
  W(fun (_,w) -> MP_TAC(ISPEC (rand(lhand w)) VAL_BOUND)) THEN
  REWRITE_TAC[DIMINDEX_8; DIMINDEX_16; DIMINDEX_32] THEN ARITH_TAC);;

let DB_IVAL_WORD_SX_16_64 = prove
 (`!b:int16. ival(word_sx b:int64) = ival b`,
  GEN_TAC THEN MATCH_MP_TAC IVAL_WORD_SX THEN
  REWRITE_TAC[DIMINDEX_16; DIMINDEX_64] THEN ARITH_TAC);;

let DB_IVAL_IWORD_16 = prove
 (`!i. --(&32768) <= i /\ i < &32768 ==> ival(iword i:int16) = i`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN ASM_REWRITE_TAC[]);;

let db_int_facts_of (ths:thm list) =
  let ok th = let c = concl th in
    type_of c = bool_ty &&
    not(exists (fun v -> type_of v = `:armstate`) (frees c)) &&
    (try let _ = find_term (fun t -> match t with
           Const("read",_) | Const("write",_) -> true | _ -> false) c in false
     with Failure _ -> true) in
  map (REWRITE_RULE[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_LE;
                    GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_ADD;
                    GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_POW])
      (filter ok ths);;

let DB_INT_FACTS_ARITH_TAC (ths:thm list) : tactic =
  MAP_EVERY MP_TAC (db_int_facts_of ths) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_EQ;
              GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL;
              GSYM INT_OF_NUM_POW] THEN
  CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN INT_ARITH_TAC;;

let DB_IVAL_WORD_COND_PRE = prove
 (`!k. k < 2 EXP 64
       ==> ival(word k:int64) = if k < 2 EXP 63 then &k else &k - &2 pow 64`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INT_IVAL; VAL_WORD; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_LT] THEN
  CONV_TAC NUM_REDUCE_CONV);;
let DB_WORD_NEG_SUB0 = WORD_RULE `!x:int64. word_neg x = word_sub (word 0) x`;;
let db_simple_fact th = let c = concl th in
  not(can (find_term (fun t -> match t with Const(("==>"|"\\/"),_) -> true | _ -> false)) c);;
let db_relevant1 (ths:thm list) (w:term) =
  let ths = filter db_simple_fact ths in
  let step vs = let sel = filter (fun th -> exists (fun v -> mem v vs) (frees(concl th))) ths in
                sel, union vs (itlist (union o frees o concl) sel []) in
  let _,vs1 = step (frees w) in
  let _,vs2 = step vs1 in
  let _,vs3 = step vs2 in
  fst(step vs3);;
let db_relevant0 (ths:thm list) (w:term) =
  let vs = frees w in
  filter (fun th -> db_simple_fact th && exists (fun v -> mem v vs) (frees(concl th))) ths;;
let rec DB_IVAL_CONV (ths:thm list) tm =
  let side t = try TAC_PROOF(([],t),DB_INT_FACTS_ARITH_TAC (db_relevant0 ths t))
               with Failure _ -> TAC_PROOF(([],t),DB_INT_FACTS_ARITH_TAC (db_relevant1 ths t)) in
  match tm with
    Comb(Const("ival",_),t) when type_of t = `:int64` ->
      (match t with
         Comb(Const("word",_),n) when is_numeral n && not(dest_numeral n </ num 2 **/ num 63) ->
           let th = MP (ISPEC n DB_IVAL_WORD_COND_PRE) (EQT_ELIM(NUM_REDUCE_CONV(mk_binop `(<):num->num->bool` n `2 EXP 64`))) in
           CONV_RULE(RAND_CONV(NUM_REDUCE_CONV THENC REWRITE_CONV[] THENC DEPTH_CONV INT_RED_CONV)) th
       | Comb(Const("word_neg",_),x) ->
           let th = ISPEC x DB_WORD_NEG_SUB0 in
           TRANS (AP_TERM `ival:int64->int` th) (DB_IVAL_CONV ths (mk_icomb(`ival:int64->int`,rhs(concl th))))
       | Comb(Const("word",_),n) ->
           let th = ISPEC n DB_IVAL_WORD_NUM in
           MP th (TAC_PROOF(([],lhand(concl th)),
             let numf l = filter (fun th -> let c = concl th in
               type_of c = bool_ty && (try type_of(lhand c) = `:num`
                                       with Failure _ -> false)) l in
             (MAP_EVERY MP_TAC (numf (db_relevant0 ths n)) THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC) ORELSE
             (MAP_EVERY MP_TAC (numf (db_relevant1 ths n)) THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC)))
       | Comb(Comb(Const(("word_add"|"word_sub") as op,_),x),y) ->
           let thx = DB_IVAL_CONV ths (mk_icomb(`ival:int64->int`,x))
           and thy = DB_IVAL_CONV ths (mk_icomb(`ival:int64->int`,y)) in
           let lem = if op = "word_add" then DB_IVAL_WORD_ADD
                     else DB_IVAL_WORD_SUB in
           let th = ISPECL [x;y] lem in
           let ant = lhand(concl th) in
           let antc = REWRITE_CONV[thx; thy] ant in
           let ath = EQ_MP (SYM antc) (side (rhs(concl antc))) in
           TRANS (MP th ath) (REWRITE_CONV[thx; thy] (rhs(rand(concl th))))
       | Comb(Const("word_zx",_),b) ->
           tryfind (fun th -> PART_MATCH lhs th tm) (CONJUNCTS DB_IVAL_WORD_ZX)
       | Comb(Const("word_sx",_),b) when type_of b = `:int16` ->
           let th1 = ISPEC b DB_IVAL_WORD_SX_16_64 in
           TRANS th1 (DB_IVAL_CONV ths (rhs(concl th1)))
       | _ -> REFL tm)
  | Comb(Const("ival",_),(Comb(Const("iword",_),i) as t))
      when type_of t = `:int16` ->
      let th = ISPEC i DB_IVAL_IWORD_16 in
      MP th (side (lhand(concl th)))
  | _ -> failwith "DB_IVAL_CONV";;

let DB_INT_DECIDE_TAC ?(rws:thm list = []) (ths:thm list) : tactic =
  REWRITE_TAC(VAL_WORD_SUB_EQ_0 :: rws) THEN
  CONV_TAC(TOP_DEPTH_CONV (VAL_NOWRAP_CONV ths)) THEN
  CONV_TAC(ONCE_DEPTH_CONV (DB_IVAL_CONV ths)) THEN
  DB_INT_FACTS_ARITH_TAC ths;;


(* ---- branchless additions ---- *)
let DB_WORD_SGT_FLAGS = prove
 (`!x y:int64.
     (~(val(word_sub x y) = 0) /\
      (ival(word_sub x y) < &0 <=> ~(ival x - ival y = ival(word_sub x y)))) <=>
     ival y < ival x`,
  BITBLAST_TAC);;

let DB_WORD_SGT_FLAGS_IMM = prove
 (`!x k. k < 2 EXP 63
     ==> ((~(val(word_sub x (word k):int64) = 0) /\
          (ival(word_sub x (word k)) < &0 <=> ~(ival x - &k = ival(word_sub x (word k))))) <=>
          &k < ival x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`x:int64`; `word k:int64`] DB_WORD_SGT_FLAGS) THEN
  ASM_SIMP_TAC[DB_IVAL_WORD_NUM]);;

let DB_WORD_SLT_FLAGS = prove
 (`!x y:int64.
     (ival(word_sub x y) < &0 <=> ~(ival x - ival y = ival(word_sub x y))) <=>
     ival y <= ival x`,
  BITBLAST_TAC);;

let DB_CCMP_GT_TAUT = TAUT
 `(~(if b then z else T) /\ ((if b then n else F) <=> (if b then v else F))) <=>
  b /\ ~z /\ (n <=> v)`;;

let DB_IVAL_WORD_COND = prove
 (`!k. k < 2 EXP 64
       ==> ival(word k:int64) = if k < 2 EXP 63 then &k else &k - &2 pow 64`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INT_IVAL; VAL_WORD; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_LT] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let db_arith_consts =
  ["=";"<";"<=";">";">=";"+";"-";"*";"DIV";"MOD";"EXP";"NUMERAL";"BIT0";"BIT1";
   "_0";"SUC";"/\\";"\\/";"~";"==>";"T";"F";"LENGTH";"val";"MIN";"MAX";"&";
   "int_lt";"int_le";"int_add";"int_sub";"int_neg";"int_mul";"int_of_num";
   "int_pow"];;

let db_is_arith_fact tm =
  type_of tm = bool_ty &&
  not(exists (fun v -> type_of v = `:armstate`) (frees tm)) &&
  (let n = ref 0 in
   let rec sz t = incr n; if !n > 300 then failwith "big" else
     match t with Comb(a,b) -> sz a; sz b | Abs(_,b) -> sz b | _ -> () in
   try sz tm; true with Failure _ -> false) &&
  forall (fun c -> mem (fst(dest_const c)) db_arith_consts) (find_terms is_const tm);;

let db_arith_facts_all asl = filter (fun th -> db_is_arith_fact (concl th)) (map snd asl);;
(* The arithmetic facts that share variables with the goal (two rounds).   *)
let db_relevant (ths:thm list) (w:term) =
  let vs0 = frees w in
  let step vs = let sel = filter (fun th -> exists (fun v -> mem v vs) (frees(concl th))) ths in
                sel, union vs (itlist (union o frees o concl) sel []) in
  let _,vs1 = step vs0 in
  let _,vs2 = step vs1 in
  fst(step vs2);;
let db_arith_facts asl = db_arith_facts_all asl;;
let db_arith_facts_for asl w = db_relevant (db_arith_facts_all asl) w;;

(* Decide a branch condition: word rewrites rws, signed compares, values as *)
(* numbers/integers, case splits on the conditionals, arithmetic.            *)
let DB_DECIDE_TAC ?(rws:thm list = []) : tactic = fun (asl,w) ->
  let ths = db_arith_facts_for asl w in
  (REWRITE_TAC(DB_CCMP_GT_TAUT :: DB_WORD_SGT_FLAGS :: DB_WORD_SLT_FLAGS :: rws) THEN
   SIMP_TAC[DB_WORD_SGT_FLAGS_IMM; ARITH] THEN
   REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
   CONV_TAC(TOP_DEPTH_CONV (VAL_NOWRAP_CONV ths)) THEN
   CONV_TAC(ONCE_DEPTH_CONV (fun t -> try DB_IVAL_CONV ths t with Failure _ ->
      match t with Comb(Const("ival",_),Comb(Const("word",_),k)) ->
        MP (ISPEC k DB_IVAL_WORD_COND)
           (TAC_PROOF(([],mk_binop `(<):num->num->bool` k `2 EXP 64`),
              MAP_EVERY MP_TAC ths THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC))
      | _ -> failwith "")) THEN
   REPEAT COND_CASES_TAC THEN
   ((fun g -> if can (find_term (fun t -> match t with Const("ival",_) | Const("int_lt",_) | Const("int_le",_) -> true | _ -> false)) (snd g)
             then NO_TAC g
             else (MAP_EVERY MP_TAC (filter (fun th -> not(can (find_term (fun t -> match t with Const("int_lt",_) | Const("int_le",_) -> true | _ -> false)) (concl th))) ths) THEN
                   CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC) g) ORELSE
   (MAP_EVERY MP_TAC (db_int_facts_of ths) THEN POP_ASSUM_LIST(MAP_EVERY MP_TAC o filter (fun th -> db_is_arith_fact (concl th))) THEN
   REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_EQ;
               GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_POW] THEN
   CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN INT_ARITH_TAC))) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Running and finishing a segment.                                          *)
(* ------------------------------------------------------------------------- *)

(* Evaluation of address terms under a sample assignment (a filter only). *)
let db_sample_env = ref ([] : (string * num) list);;
let db_sample v = let n = fst(dest_var v) in
  try assoc n !db_sample_env with Failure _ ->
    let x = Num.num_of_int (1000003 + 7919 * (Hashtbl.hash n mod 1000)) in
    db_sample_env := (n,x) :: !db_sample_env; x;;
let db_two64 = Num.power_num (Num.num_of_int 2) (Num.num_of_int 64);;
let rec db_eval_num tm = match tm with
    Comb(Comb(Const("+",_),a),b) -> db_eval_num a +/ db_eval_num b
  | Comb(Comb(Const("-",_),a),b) -> let x = db_eval_num a -/ db_eval_num b in if x </ Num.num_of_int 0 then Num.num_of_int 0 else x
  | Comb(Comb(Const("*",_),a),b) -> db_eval_num a */ db_eval_num b
  | Comb(Comb(Const("EXP",_),a),b) -> Num.power_num (db_eval_num a) (db_eval_num b)
  | Var(_,ty) when ty = `:num` -> db_sample tm
  | _ when is_numeral tm -> dest_numeral tm
  | _ -> failwith "db_eval_num";;
let rec db_eval_word tm = match tm with
    Comb(Comb(Const("word_add",_),a),b) -> mod_num (db_eval_word a +/ db_eval_word b) db_two64
  | Comb(Comb(Const("word_sub",_),a),b) -> mod_num (db_eval_word a -/ db_eval_word b +/ db_two64) db_two64
  | Comb(Const("word_neg",_),a) -> mod_num (db_two64 -/ db_eval_word a) db_two64
  | Comb(Const("word",_),n) -> mod_num (db_eval_num n) db_two64
  | Var(_,ty) when ty = `:int64` -> db_sample (mk_var(fst(dest_var tm),`:num`))
  | _ -> failwith "db_eval_word";;
let db_maybe_equal a b = try db_eval_word a =/ db_eval_word b with Failure _ -> true;;
let db_conj_report (tac:tactic) : tactic = fun (asl,w) ->
  try tac (asl,w) with Failure m ->
    let s = string_of_term w in
    Printf.printf "CONJ FAILED (%s): %s\n%!" m (if String.length s > 1500 then String.sub s 0 1500 else s);
    failwith m;;
let DB_ARITH_TAC : tactic = fun (asl,w) ->
  if not (db_is_arith_fact w) then failwith "DB_ARITH_TAC: not arithmetic" else
  let facts = db_arith_facts_all asl in
  let att l (asl,w) = (MAP_EVERY MP_TAC l THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC) (asl,w) in
  (FIRST_ASSUM ACCEPT_TAC ORELSE att (db_relevant0 facts w) ORELSE att (db_relevant1 facts w) ORELSE
   att (db_relevant facts w)) (asl,w);;

let DB_WORD_SUB_ADD = WORD_RULE `!x y:int64. word_add (word_sub x y) y = x`;;
let DB_WORD_SHIFT = prove
 (`!x y. y = x + 2 EXP 64 \/ x = y + 2 EXP 64 \/ x = y ==> word x:int64 = word y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[WORD_EQ; DIMINDEX_64; CONG] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[MOD_MULT_ADD; ARITH_RULE `2 EXP 64 + x = 1 * 2 EXP 64 + x`]);;
let rec DB_STRIP_ADD_TAC : tactic = fun (asl,w) ->
  match w with
    Comb(Comb(Const("=",_),Comb(Comb(Const("word_add",_),a),_)),Comb(Comb(Const("word_add",_),b),_)) when a = b ->
      (AP_TERM_TAC THEN DB_STRIP_ADD_TAC) (asl,w)
  | _ -> ALL_TAC (asl,w);;
let DB_WORD_NEG_NUM = prove
 (`!b. b < 2 EXP 64 ==> word_neg (word b):int64 = word (2 EXP 64 - b)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_RULE `word_neg (x:int64) = word_sub (word 0) x`] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUB; VAL_WORD; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `0 MOD n = 0`; ADD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;
let DB_WORD_SUB_AS_NEG = WORD_RULE `!x y:int64. word_sub x y = word_add x (word_neg y)`;;
let DB_FAST_WEQ_TAC : tactic = fun (asl,w) ->
  let negconv tm = match tm with
      Comb(Const("word_neg",_),Comb(Const("word",_),b)) when type_of tm = `:int64` ->
        MP (ISPEC b DB_WORD_NEG_NUM) (TAC_PROOF((asl,mk_binop `(<):num->num->bool` b `2 EXP 64`), DB_ARITH_TAC))
    | Comb(Comb(Const("word_sub",_),x),(Comb(Const("word",_),b) as y)) when type_of tm = `:int64` ->
        ISPECL [x;y] DB_WORD_SUB_AS_NEG
    | _ -> failwith "negconv" in
  (CONV_TAC(TOP_DEPTH_CONV negconv) THEN
   REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
   (fun (asl,w) -> match w with
      Comb(Comb(Const("=",_),Comb(Const("word",_),x)),Comb(Const("word",_),y)) ->
        let pick = try let d = db_eval_num x -/ db_eval_num y in
                       if d =/ db_two64 then 2 else if d =/ minus_num db_two64 then 1 else 3
                   with Failure _ -> 0 in
        let sel = match pick with
            1 -> DISJ1_TAC | 2 -> DISJ2_TAC THEN DISJ1_TAC | 3 -> DISJ2_TAC THEN DISJ2_TAC | _ -> ALL_TAC in
        (MATCH_MP_TAC DB_WORD_SHIFT THEN sel THEN DB_ARITH_TAC) (asl,w)
    | _ -> failwith "DB_FAST_WEQ_TAC")) (asl,w);;
let DB_WORD_SUB_NUM = prove
 (`!x y. y <= x ==> word(x - y):int64 = word_sub (word x) (word y)`,
  SIMP_TAC[WORD_SUB]);;
let DB_WORD_EQ_TAC : tactic = fun (asl,w) ->
  let ths = db_arith_facts_for asl w in
  let intsub tm = match tm with
      Comb(Const("int_of_num",_),Comb(Comb(Const("-",_),a),b)) ->
        let le = TAC_PROOF((asl,mk_binop `(<=):num->num->bool` b a),DB_ARITH_TAC) in
        MP (ISPECL [b;a] INT_OF_NUM_SUB) le
    | _ -> failwith "intsub" in
  let subconv tm = match tm with
      Comb(Const("word",_),(Comb(Comb(Const("-",_),x),y))) when type_of tm = `:int64` ->
        let th = ISPECL [x;y] DB_WORD_SUB_NUM in
        MP th (TAC_PROOF((asl,lhand(concl th)),DB_ARITH_TAC))
    | _ -> failwith "" in
  (DB_STRIP_ADD_TAC THEN
   (DB_FAST_WEQ_TAC ORELSE
   (fun g -> match snd g with
      Comb(Comb(Const("=",_),Comb(Const("word",_),_)),Comb(Const("word",_),_)) ->
        (MATCH_MP_TAC DB_WORD_SHIFT THEN DB_ARITH_TAC) g
    | _ -> failwith "") ORELSE
   (CONV_TAC(TOP_DEPTH_CONV subconv) THEN
   ONCE_REWRITE_TAC[GSYM IVAL_EQ] THEN
   CONV_TAC(ONCE_DEPTH_CONV (DB_IVAL_CONV ths)) THEN
   CONV_TAC(TOP_DEPTH_CONV intsub) THEN
   REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN
   CONV_TAC(TOP_DEPTH_CONV intsub) THEN
   CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN INT_ARITH_TAC))) (asl,w);;
let DB_SUBSET_WORD = prove
 (`!p x k l. x + k <= l ==> memrange(word (p + x):int64,k) SUBSET memrange(word p,l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_ADD] THEN MATCH_MP_TAC DB_SUBSET_OFFSETS0 THEN ASM_REWRITE_TAC[]);;
let DB_WORD_SPLIT_TAC (p:term) : tactic = fun (asl,w) ->
  (* goal memrange(word t,k) SUBSET memrange(word p,l) *)
  let t = rand(lhand(rand(lhand w))) in
  let x = mk_binop `(-):num->num->num` t p in
  let eq = ARITH_RULE(mk_eq(t, mk_binop `(+):num->num->num` p x)) in
  (GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV) [eq] THEN
   MATCH_MP_TAC DB_SUBSET_WORD THEN DB_ARITH_TAC) (asl,w);;
let DB_NORM_CONV =
  let rec wconv tm = match tm with
      Comb(Const("word",_),t) when not(is_numeral t) && type_of t = `:num` ->
        RAND_CONV NUM_NORMALIZE_CONV tm
    | Comb(Comb(Const("EL",_),t),_) when not(is_numeral t) ->
        RATOR_CONV(RAND_CONV NUM_NORMALIZE_CONV) tm
    | Comb(Const("bytelist",_),Comb(Comb(Const(",",_),a),n)) when not(is_numeral n) ->
        RAND_CONV(LAND_CONV(TRY_CONV(ONCE_DEPTH_CONV wconv)) THENC RAND_CONV NUM_NORMALIZE_CONV) tm
    | _ -> failwith "" in
  REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; WORD_ADD_0; DB_WORD_SUB_ADD] THENC
  ONCE_DEPTH_CONV wconv;;

let DB_STACK_REBASE = prove
 (`(!sp t. word_add (word_sub sp (word 240)) (word t):int64 =
           word_add (word_sub sp (word 288)) (word (t + 48))) /\
   (!sp. word_sub sp (word 240):int64 = word_add (word_sub sp (word 288)) (word 48))`,
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

(* word t = word (t - 2^64) when t >= 2^64 (a wrapped negative offset) *)
let DB_UNWRAP_CONV (asl:(string*thm) list) : conv = fun tm ->
  match tm with
    Comb(Const("word",_),t) when type_of tm = `:int64` &&
      exists (fun s -> is_numeral s && not(dest_numeral s </ num 2 **/ num 63))
        (striplist (dest_binop `(+):num->num->num`) t) ->
      let t' = mk_binop `(-):num->num->num` t `2 EXP 64` in
      let th = ISPECL [t; t'] DB_WORD_SHIFT in
      MP th (TAC_PROOF((asl,lhand(concl th)),
               DISJ2_TAC THEN DISJ1_TAC THEN DB_ARITH_TAC))
  | _ -> failwith "DB_UNWRAP_CONV";;
(* |- p SUBSET u for a part p of the union u (syntactically). *)
let rec db_in_union (p:term) (u:term) : thm =
  if u = p then ISPEC p SUBSET_REFL else
  match u with
    Comb(Comb(Const("UNION",_),a),b) ->
      (try let th = db_in_union p a in
           MATCH_MP SUBSET_TRANS (CONJ th (ISPECL [a;b] (CONJUNCT1 SUBSET_UNION)))
       with Failure _ ->
           let th = db_in_union p b in
           MATCH_MP SUBSET_TRANS (CONJ th (ISPECL [b;a] (CONJUNCT2 SUBSET_UNION))))
  | _ -> failwith "db_in_union";;
(* memrange(a,k) SUBSET a union of regions, by the part with the same base. *)
let DB_SUBSET_NEG = prove
 (`!(base:int64) x off k l.
     off <= x /\ (x - off) + k <= l
     ==> memrange(word_add (word_add base (word x)) (word_neg (word off)),k) SUBSET
         memrange(base,l)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_add (word_add base (word x)) (word_neg (word off)):int64 =
                word_add base (word(x - off))` SUBST1_TAC THENL
   [ASM_SIMP_TAC[WORD_SUB] THEN CONV_TAC WORD_RULE;
    MATCH_MP_TAC DB_SUBSET_OFFSETS0 THEN ASM_REWRITE_TAC[]]);;
let DB_WADD2 = prove
 (`!(b:int64) x y. word_add (word_add b (word x)) (word y) = word_add b (word(x + y))`,
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;
let DB_NEG_CONST_CONV : conv = fun tm ->
  match tm with
    Comb(Const("word",_),n) when type_of tm = `:int64` && is_numeral n &&
        not(dest_numeral n </ num 2 **/ num 63) ->
      let c = mk_numeral(num 2 **/ num 64 -/ dest_numeral n) in
      let th = WORD_REDUCE_CONV(mk_comb(`word_neg:int64->int64`,mk_comb(`word:num->int64`,c))) in
      SYM th
  | _ -> failwith "DB_NEG_CONST_CONV";;
let DB_NEG_SUBSET_TAC : tactic = fun (asl,w) ->
  let parts = striplist (dest_binop `(UNION):(int64->bool)->(int64->bool)->(int64->bool)`) (rand w) in
  let one p g =
    let ok = TAC_PROOF((fst g,mk_icomb(mk_icomb(`(SUBSET):(int64->bool)->(int64->bool)->bool`,lhand(snd g)),p)),
       MATCH_MP_TAC DB_SUBSET_NEG THEN CONJ_TAC THEN DB_ARITH_TAC) in
    ACCEPT_TAC (MATCH_MP SUBSET_TRANS (CONJ ok (db_in_union p (rand(snd g))))) g in
  (CONV_TAC(LAND_CONV(RAND_CONV(LAND_CONV(TOP_DEPTH_CONV DB_NEG_CONST_CONV)))) THEN
   CONV_TAC(LAND_CONV(RAND_CONV(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD; DB_WADD2])))) THEN
   (fun g -> match lhand(rand(lhand(snd g))) with
      Comb(Comb(Const("word_add",_),Comb(Comb(Const("word_add",_),_),Comb(Const("word",_),_))),
           Comb(Const("word_neg",_),Comb(Const("word",_),_))) -> FIRST (map one parts) g
    | _ -> failwith "DB_NEG_SUBSET_TAC")) (asl,w);;
let DB_ADDR_SUBSET_TAC : tactic = fun (asl,w) ->
  let parts = striplist (dest_binop `(UNION):(int64->bool)->(int64->bool)->(int64->bool)`) (rand w) in
  let sub l p = mk_icomb(mk_icomb(`(SUBSET):(int64->bool)->(int64->bool)->bool`,l),p) in
  let one p g =
    let ok = TAC_PROOF((fst g,sub (lhand(snd g)) p),
       FIRST [MATCH_ACCEPT_TAC SUBSET_REFL;
              MATCH_MP_TAC DB_SUBSET_PREFIX THEN DB_ARITH_TAC;
              MATCH_MP_TAC DB_SUBSET_OFFSETS0 THEN DB_ARITH_TAC;
              MATCH_MP_TAC DB_SUBSET_OFFSETS THEN DB_ARITH_TAC;
              (match p with Comb(_,Comb(Comb(_,Comb(Const("word",_),pv)),_)) when is_var pv -> DB_WORD_SPLIT_TAC pv
                | _ -> NO_TAC)]) in
    ACCEPT_TAC (MATCH_MP SUBSET_TRANS (CONJ ok (db_in_union p (rand(snd g))))) g in
  (FIRST_ASSUM ACCEPT_TAC ORELSE DB_NEG_SUBSET_TAC ORELSE
   (CONV_TAC(LAND_CONV(RAND_CONV(LAND_CONV DB_NORM_CONV))) THEN
    TRY(GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [CONJUNCT1 DB_STACK_REBASE]) THEN
    TRY(GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [CONJUNCT2 DB_STACK_REBASE]) THEN
    CONV_TAC(LAND_CONV(RAND_CONV(LAND_CONV DB_NORM_CONV))) THEN
    TRY(CONV_TAC(LAND_CONV(RAND_CONV(LAND_CONV(ONCE_DEPTH_CONV(DB_UNWRAP_CONV asl)))))) THEN
    FIRST (map one parts))) (asl,w);;

let DB_EVENTS_TAC : tactic = fun (asl,w) ->
  let v,bod = dest_exists w in
  let eqt = lhand bod in
  let t = lhs eqt and e = rand(rhs eqt) in
  let th = snd(find (fun (_,th) -> is_eq(concl th) && lhs(concl th) = t) asl) in
  let x = events_prefix e (rhs(concl th)) in
  (EXISTS_TAC x THEN CONJ_TAC THENL
    [REWRITE_TAC[th; APPEND; GSYM APPEND_ASSOC; APPEND_NIL];
     REWRITE_TAC[MEMACCESS_INSET_CLAUSES; MEMACCESS_INSET_APPEND; APPEND_NIL;
                 event_loads; event_stores; EMPTY_SUBSET] THEN
     REPEAT CONJ_TAC THEN db_conj_report (FIRST_ASSUM ACCEPT_TAC ORELSE DB_ADDR_SUBSET_TAC)]) (asl,w);;

let db_is_read_fact s th = match concl th with
    Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),s')),_) -> s' = s
  | _ -> false;;

(* A fact read c s = v of the goal from the facts at s, up to the normal    *)
(* form of addresses and numbers, with the facts at the other states (the   *)
(* values read from them) as rewrites.                                       *)
let DB_REG_TAC : tactic = fun (asl,w) ->
  let s = rand(lhs w) and c = rand(rator(lhs w)) in
  try FIRST_ASSUM ACCEPT_TAC (asl,w) with Failure _ ->
  let olds = map snd (filter (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),_),_)),s')),_) -> s' <> s && is_var s'
    | _ -> false) asl) in
  let olds' = map (CONV_RULE DB_NORM_CONV) olds in
  let norm = DB_NORM_CONV THENC REWRITE_CONV olds' THENC DB_NORM_CONV in
  let nc = rhs(concl(DB_NORM_CONV c)) in
  let cands = filter (fun (_,th) -> db_is_read_fact s th &&
                (let c' = rand(rator(lhs(concl th))) in c' = c ||
                 (try rhs(concl(DB_NORM_CONV c')) = nc with Failure _ -> false))) asl in
  let try_cand (_,th) g =
    (MP_TAC th THEN CONV_TAC(BINOP_CONV norm) THEN
     DISCH_THEN(fun th' -> REWRITE_TAC[th']) THEN TRY DB_WORD_EQ_TAC THEN NO_TAC) g in
  let sublist g =
    (* bytelist(word_add A (word j),k) from bytelist(A,p) *)
    match c with
      Comb(Comb(Const(":>",_),_),Comb(Const("bytelist",_),Comb(Comb(Const(",",_),a),k))) ->
        let a0,j = (match a with Comb(Comb(Const("word_add",_),a0),Comb(Const("word",_),j)) -> a0,j
                    | _ -> a,`0`) in
        let big = find (fun (_,th) -> db_is_read_fact s th &&
             (match rand(rator(lhs(concl th))) with
                Comb(Comb(Const(":>",_),_),Comb(Const("bytelist",_),Comb(Comb(Const(",",_),a'),_))) -> a' = a0
              | _ -> false)) asl in
        let p = rand(rand(rand(rand(rator(lhs(concl(snd big))))))) in
        (MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`; a0; j; k; p; s] READ_BYTELIST_SUB_LIST) THEN
         REWRITE_TAC[snd big; WORD_ADD_0] THEN ANTS_TAC THENL [DB_ARITH_TAC; ALL_TAC] THEN
         DISCH_THEN SUBST1_TAC THEN TRY REFL_TAC THEN FIRST_ASSUM ACCEPT_TAC) g
    | _ -> failwith "sublist" in
  (CONV_TAC(BINOP_CONV norm) THEN
   FIRST (map try_cand cands @ [sublist;
     REWRITE_TAC[READ_COMPONENT_COMPOSE; bytelist_clauses] THEN NO_TAC])) (asl,w);;

let DB_PRE_TAC : tactic =
  REPEAT CONJ_TAC THEN
  db_conj_report (FIRST [FIRST_ASSUM ACCEPT_TAC;
         (fun (asl,w) -> if is_exists w then DB_EVENTS_TAC (asl,w) else failwith "");
         DB_REG_TAC]);;

let DB_TO_TAC0 (which:int) (nmeas:term) (ghosts:term list) : tactic =
  ALL_TAC THEN
  (fun (asl,w) -> if is_conj w then (CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC]) (asl,w) else ALL_TAC (asl,w)) THEN
  DISJ2_TAC THEN EXISTS_TAC nmeas THEN CONJ_TAC THENL [DB_ARITH_TAC; ALL_TAC] THEN
  (if which = 0 then DISJ1_TAC else if which = 1 then DISJ2_TAC THEN DISJ1_TAC
   else DISJ2_TAC THEN DISJ2_TAC THEN CONJ_TAC THENL [REFL_TAC; ALL_TAC]) THEN
  MAP_EVERY EXISTS_TAC ghosts THEN
  (if which = 2 then ALL_TAC else CONJ_TAC THENL [DB_ARITH_TAC; ALL_TAC]) THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC ORELSE
    (REPEAT CONJ_TAC THEN (fun (asl,w) ->
       let ths = flat (map (CONJUNCTS o snd) asl) in
       try ACCEPT_TAC (find (fun th -> concl th = w) ths) (asl,w)
       with Failure _ -> (DB_ARITH_TAC ORELSE (fun _ -> failwith ("static: " ^ string_of_term w))) (asl,w))); ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
                  REPEAT CONJ_TAC THEN DB_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DB_PRE_TAC;;

let DB_TO_TAC which nmeas ghosts = BSTEP_FINAL_TAC THEN DB_TO_TAC0 which nmeas ghosts;;

(* Step one instruction at a time (deciding branches) until the PC is       *)
(* word(pc + k) for k in stops.                                              *)
let db_state_num (w:term) =
  let s = fst(dest_var(rand w)) in int_of_string(String.sub s 1 (String.length s - 1));;
let db_pc_value asl s =
  let _,th = find (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),s')),_) -> s' = s
    | _ -> false) asl in rhs(concl th);;
let rec DB_RUN_TAC ?(rws:thm list = []) ?(folds:thm list = []) (stops:int list) : tactic = fun (asl,w) ->
  let s = rand w in
  let v = db_pc_value asl s in
  let at_stop = match v with
      Comb(Const("word",_),Comb(Comb(Const("+",_),_),k)) when is_numeral k ->
        mem (dest_small_numeral k) stops
    | _ -> false in
  if at_stop || is_var v then ALL_TAC (asl,w) else
  if is_cond v then
    let c = lhand(rator v) in
    let pth = snd(find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),s')),_) -> s' = s
      | _ -> false) asl) in
    let dth = try TAC_PROOF((asl,c),DB_DECIDE_TAC ~rws) with Failure _ ->
              TAC_PROOF((asl,mk_neg c),DB_DECIDE_TAC ~rws) in
    (UNDISCH_THEN (concl pth) (fun th -> ASSUME_TAC(REWRITE_RULE[dth] th)) THEN
     ASSUME_TAC dth THEN DB_RUN_TAC ~rws ~folds stops) (asl,w) else
  let i = db_state_num w + 1 in
  (ARM_BSTEP_DECIDE_TAC ~rewrites:rws ~folds ~decide:(DB_DECIDE_TAC ~rws) db_exec (i--i) THEN
   DB_RUN_TAC ~rws ~folds stops) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* The flush of the deferred copy (MemCopy64 at base + op).                  *)
(* ------------------------------------------------------------------------- *)

let db_flush_stmt = parse_term ("!e base op m L src dl D pc rw sp returnaddress x19 x20 x21 x29 ea el ev ip li.
  memmove_correct_safe_contract (imp \"memmove\") ea el ev /\\
  aligned 4096 (word pc:int64) /\\
  pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\\
  elf_relocated_data (word(pc + libsnappy_rw)) rw (snappy_libsnappy_gcc12_O2_relocated pc imp) /\\
  aligned 16 sp /\\ LENGTH L = op /\\ LENGTH D = dl /\\ dl <= 64 /\\ op + 64 <= m /\\
  val base + m < 2 EXP 64 /\\
  nonoverlapping (word_add base (word op),dl) (src,dl) /\\
  nonoverlapping (src,dl) (word_sub sp (word 288),288) /\\
  memrange(src,64) SUBSET " ^ db_rd ^ " /\\
  nonoverlapping (base,m) (word pc,libsnappy_rw + libsnappy_rw_size) /\\
  nonoverlapping (base,m) (ea,el) /\\
  nonoverlapping (word_sub sp (word 288),288) (word pc,libsnappy_rw + libsnappy_rw_size) /\\
  nonoverlapping (word_sub sp (word 288),288) (ea,el) /\\
  nonoverlapping (base,m) (word_sub sp (word 288),288)
  ==> ensures arm
   (\\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\\
        read PC s = word(pc + MemCopy64__charp_voidp_ulong) /\\
        read SP s = word_sub sp (word 240) /\\ read X30 s = returnaddress /\\
        read X19 s = x19 /\\ read X20 s = x20 /\\ read X21 s = x21 /\\ read X29 s = x29 /\\
        read X0 s = word_add base (word op) /\\ read X1 s = src /\\ read X2 s = word dl /\\
        read (memory :> bytelist(base,op)) s = L /\\
        read (memory :> bytelist(src,dl)) s = D /\\
        read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s = rw /\\
        read (memory :> bytes(ea,el)) s = ev /\\ read events s = e)
   (\\s. read PC s = returnaddress /\\ read SP s = word_sub sp (word 240) /\\
        read X19 s = x19 /\\ read X20 s = x20 /\\ read X21 s = x21 /\\ read X29 s = x29 /\\
        read (memory :> bytelist(base,op + dl)) s = APPEND L D /\\
        ?e2. read events s = APPEND e2 e /\\ memaccess_inset e2 " ^ db_rd ^ " " ^ db_wr ^ ")
   (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [SP; X18; X19; X20; X21; X29; X30] ,,
    MAYCHANGE [memory :> bytes(word_sub sp (word 288),48)] ,, MAYCHANGE [memory :> bytes(base,m)])");;
let NOV_TAC tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
   MATCH_MP_TAC DB_NONOVERLAPPING_OFFSETS0 THEN ASM_ARITH_TAC; ALL_TAC];;
let DB_UNION_SUBSET_TAC : tactic =
  REWRITE_TAC[WORD_RULE `word_sub (word_sub sp (word 240)) (word 48):int64 = word_sub sp (word 288)`] THEN
  REWRITE_TAC[UNION_SUBSET] THEN REPEAT CONJ_TAC THEN
  W(fun (asl,w) ->
    let parts = striplist (dest_binop `(UNION):(int64->bool)->(int64->bool)->(int64->bool)`) (rand w) in
    let l = lhand w in
    let sub p = mk_icomb(mk_icomb(`(SUBSET):(int64->bool)->(int64->bool)->bool`,l),p) in
    let try_part p g =
      let ok = TAC_PROOF((asl,sub p),
          FIRST [MATCH_ACCEPT_TAC SUBSET_REFL; FIRST_ASSUM ACCEPT_TAC;
                 MATCH_MP_TAC DB_SUBSET_OFFSETS0 THEN ASM_ARITH_TAC; MATCH_MP_TAC DB_SUBSET_PREFIX THEN ARITH_TAC;
                 MATCH_MP_TAC DB_SUBSET_OFFSETS THEN ASM_ARITH_TAC]) in
      (MP_TAC ok THEN SET_TAC[]) g in
    FIRST (FIRST_ASSUM ACCEPT_TAC :: map try_part parts));;
let DB_FLUSH = prove(db_flush_stmt,
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  NOV_TAC `nonoverlapping (base:int64,op) (word_add base (word op),32)` THEN
  NOV_TAC `nonoverlapping (base:int64,op) (word_add (word_add base (word op)) (word 32),32)` THEN
  MAP_EVERY (fun r -> MP_TAC(SPECL [`base:int64`; `m:num`; `op:num`; `64`] DB_NONOVERLAPPING_SUB) THEN
     DISCH_THEN(MP_TAC o SPECL r) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC)
   [[`word pc:int64`; `129968 + 1120`]; [`ea:int64`; `el:num`]; [`word_sub sp (word 288):int64`; `288`]] THEN
  SUBGOAL_THEN `val(word dl:int64) = dl` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  X_CHOOSE_TAC `y:num` (prove(`?z. read (memory :> bytes(src:int64,dl)) s0 = z`, MESON_TAC[])) THEN
  ARM_BSTEP_CONTRACT_TAC db_exec SNAPPY_MEM_COPY64_GCC12_O2_IMAGE_SUBROUTINE_SAFE
   [`read events s`; `read X0 s`; `read X1 s`; `read X2 s`; `y:num`;
    `pc:num`; `rw:num`; `read SP s`; `read X30 s`; `read X19 s`; `read X20 s`; `read X21 s`; `read X29 s`;
    `ea:int64`; `el:num`; `ev:num`] "s1" THEN
  BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[READ_BYTELIST_SPLIT] THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `read (memory :> bytelist(src:int64,dl)) s0` THEN
    CONJ_TAC THENL [MATCH_MP_TAC DB_BYTELIST_OF_BYTES THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [W(fun (_,w) -> EXISTS_TAC (lhand(lhs(lhand(snd(dest_exists w)))))) THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MEMACCESS_INSET_MONO THEN
    FIRST_ASSUM(fun th -> match concl th with Comb(Comb(Comb(Const("memaccess_inset",_),_),r),w) ->
      EXISTS_TAC r THEN EXISTS_TAC w THEN REWRITE_TAC[th] | _ -> NO_TAC) THEN
    CONJ_TAC THEN DB_UNION_SUBSET_TAC;
    ALL_TAC] THEN
  W(fun (asl,w) ->
   let fth = snd(find (fun (_,th) -> bstep_is_frame (concl th) && rand(concl th) = `s1:armstate`) asl) in
   let f = rator(rator(concl fth)) and c = rator(rator w) in
   let f' = rand(concl(REWRITE_CONV[MAYCHANGE_LID] f)) in
   let sth = db_frame_subsumed asl (FIRST[MATCH_MP_TAC DB_SUBSET_OFFSETS0 THEN ASM_ARITH_TAC;
       REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN MATCH_MP_TAC DB_SUBSET_OFFSETS0 THEN ASM_ARITH_TAC]) f' c in
   MATCH_MP_TAC DB_SUBSUMED_APPLY THEN EXISTS_TAC f' THEN CONJ_TAC THENL
    [ACCEPT_TAC sth; MP_TAC fth THEN REWRITE_TAC[MAYCHANGE_LID]]));;

(* ------------------------------------------------------------------------- *)
(* The model: one tag at position h (pure lemmas).                           *)
(* ------------------------------------------------------------------------- *)

let DB_NONOVERLAPPING_SUB2 = prove
 (`!(base:int64) m x k b l.
     nonoverlapping (b,l) (base,m) /\ x + k <= m
     ==> nonoverlapping (b,l) (word_add base (word x),k)`,
  MESON_TAC[DB_NONOVERLAPPING_SUB; NONOVERLAPPING_SYM]);;
let db_static_tm = parse_term db_static;;
let db_inst_static l = vsubst (map (fun (v,t) -> (t, mk_var(v,type_of t))) l) db_static_tm;;
let DB_STEP_LIT_STMT =
  let hyp = parse_term "LENGTH (inp:byte list) = li /\\ val(EL h inp) MOD 4 = 0 /\\ val(EL h inp) DIV 4 = d /\\ d < 60 /\\
     h + 70 <= li /\\ op + dl + 64 <= m /\\
     nonoverlapping (ip,li) (base:int64,m) /\\ nonoverlapping (ip,li) (word_sub sp (word 288),288)" in
  let nw = db_inst_static ["h",`h + d + 2`; "op",`op + dl:num`; "dl",`d + 1`; "dsrc",`word_add ip (word (h + 1)):int64`;
                           "ob",`APPEND ob db:byte list`; "db",`SUB_LIST(h + 1,d + 1) inp:byte list`; "k",`SUC k`] in
  list_mk_forall(frees (mk_conj(hyp,db_static_tm)), mk_imp(mk_conj(hyp,db_static_tm), nw));;
print_term DB_STEP_LIT_STMT;;
let DB_STEP_LIT = prove(DB_STEP_LIT_STMT,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[SNAPPY_STEPS_SUC; snappy_bind] THEN
    MP_TAC(SPECL [`m:num`; `inp:byte list`; `APPEND ob db:byte list`; `h:num`] SNAPPY_TAG_STEP_LITERAL_AT) THEN
    ASM_REWRITE_TAC[LENGTH_APPEND] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ARITH_RULE `h + d + 2 = h + d + 2`];
    ASM_REWRITE_TAC[LENGTH_APPEND];
    REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    MATCH_MP_TAC DB_NONOVERLAPPING_SUB THEN EXISTS_TAC `m:num` THEN CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    MATCH_MP_TAC DB_NONOVERLAPPING_SUB2 THEN EXISTS_TAC `li:num` THEN CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC DB_NONOVERLAPPING_SUB THEN EXISTS_TAC `li:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC(SET_RULE `s SUBSET a ==> s SUBSET a UNION b`) THEN
    MATCH_MP_TAC DB_SUBSET_OFFSETS0 THEN ASM_ARITH_TAC]);;
let db_mk_lemma hyp nw =
  let hyp = parse_term hyp in
  list_mk_forall(frees (mk_conj(hyp,db_static_tm)), mk_imp(mk_conj(hyp,db_static_tm), nw));;
let db_safe = `word_add (word_sub sp (word 240)) (word 176):int64`;;
let DB_SAFE_FACTS = prove
 (`!sp:int64. nonoverlapping (a:int64,0) (b,0) /\
     nonoverlapping (word_add (word_sub sp (word 240)) (word 176),0) (word_sub sp (word 288),288) /\
     memrange(word_add (word_sub sp (word 240)) (word 176),64) SUBSET memrange(word_sub sp (word 288),288)`,
  GEN_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_TRIVIAL THEN ARITH_TAC;
    MATCH_MP_TAC NONOVERLAPPING_TRIVIAL THEN ARITH_TAC;
    REWRITE_TAC[CONJUNCT1 DB_STACK_REBASE] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC DB_SUBSET_OFFSETS0 THEN ARITH_TAC]);;
let DB_STEP_COPY_DEFER = prove(db_mk_lemma
  "LENGTH (inp:byte list) = li /\\
   snappy_tag_step m (SUB_LIST(h,li - h) inp) (APPEND ob db) = snappy_copy_tag m off len (SUB_LIST(h',li - h') inp) (APPEND ob db) /\\
   len <= off /\\ off <= op + dl /\\ 1 <= len /\\ len <= 64 /\\ op + dl + 64 <= m /\\ m < 2 EXP 32 /\\
   nonoverlapping (base:int64,m) (word_sub sp (word 288),288)"
  (db_inst_static ["h",`h':num`; "op",`op + dl:num`; "dl",`len:num`; "dsrc",`word_add base (word ((op + dl) - off)):int64`;
                   "ob",`APPEND ob db:byte list`; "db",`SUB_LIST((op + dl) - off,len) (APPEND ob db):byte list`; "k",`SUC k`]),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[SNAPPY_STEPS_SUC; snappy_bind; snappy_copy_tag; LENGTH_APPEND] THEN
    COND_CASES_TAC THENL [ALL_TAC; POP_ASSUM MP_TAC THEN ASM_ARITH_TAC] THEN
    REWRITE_TAC[option_INJ; PAIR_EQ] THEN
    MP_TAC(SPECL [`off:num`; `len:num`; `APPEND ob db:byte list`] SNAPPY_COPY_NONOVERLAP) THEN
    ASM_REWRITE_TAC[LENGTH_APPEND] THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[];
    ASM_REWRITE_TAC[LENGTH_APPEND];
    REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_APPEND] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN MATCH_MP_TAC DB_NONOVERLAPPING_OFFSETS THEN
    MP_TAC(ISPEC `base:int64` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC DB_NONOVERLAPPING_SUB THEN EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC(SET_RULE `s SUBSET b ==> s SUBSET a UNION b UNION c`) THEN
    MATCH_MP_TAC DB_SUBSET_OFFSETS0 THEN ASM_ARITH_TAC]);;
let DB_STEP_PATTERN = prove(db_mk_lemma
  "LENGTH (inp:byte list) = li /\\
   snappy_tag_step m (SUB_LIST(h,li - h) inp) (APPEND ob db) = snappy_copy_tag m off len (SUB_LIST(h',li - h') inp) (APPEND ob db) /\\
   1 <= off /\\ off <= op + dl /\\ len <= 64 /\\ op + dl + len <= m"
  (db_inst_static ["h",`h':num`; "op",`op + dl + len:num`; "dl",`0`; "dsrc",db_safe;
                   "ob",`snappy_copy off len (APPEND ob db):byte list`; "db",`[]:byte list`; "k",`SUC k`]),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[DB_SAFE_FACTS; LENGTH; LE_0] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[SNAPPY_STEPS_SUC; snappy_bind; snappy_copy_tag; LENGTH_APPEND; APPEND_NIL] THEN
    COND_CASES_TAC THENL [REWRITE_TAC[]; POP_ASSUM MP_TAC THEN ASM_ARITH_TAC];
    ASM_REWRITE_TAC[LENGTH_SNAPPY_COPY; LENGTH_APPEND] THEN ARITH_TAC;
    MATCH_MP_TAC(SET_RULE `s SUBSET c ==> s SUBSET a UNION b UNION c UNION d`) THEN
    REWRITE_TAC[DB_SAFE_FACTS]]);;
let DB_STATIC_FLUSHED = prove(db_mk_lemma "T"
  (db_inst_static ["op",`op + dl:num`; "dl",`0`; "dsrc",db_safe; "ob",`APPEND ob db:byte list`; "db",`[]:byte list`]),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[DB_SAFE_FACTS; LENGTH; LE_0; APPEND_NIL] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[LENGTH_APPEND];
    MATCH_MP_TAC(SET_RULE `s SUBSET c ==> s SUBSET a UNION b UNION c UNION d`) THEN
    REWRITE_TAC[DB_SAFE_FACTS]]);;
let DB_BYTES16_EL = prove
 (`!(a:int64) l n i s.
     read (memory :> bytelist(a,n)) s = l /\ i + 2 <= n
     ==> read (memory :> bytes16 (word_add a (word i))) s =
         word(val(EL i l) + 256 * val(EL (i + 1) l))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[el 4 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[EL_READ_BYTELIST; ARITH_RULE `i + 2 <= n ==> i < n /\ i + 1 < n`] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  SIMP_TAC[VAL_WORD_JOIN_SIMPLE; DIMINDEX_8; DIMINDEX_16; ARITH; VAL_WORD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `read (memory :> bytes8 (word_add a (word i))) s` VAL_BOUND) THEN
  MP_TAC(ISPEC `read (memory :> bytes8 (word_add a (word (i + 1)))) s` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
  W(fun (_,w) -> MP_TAC(SPECL [lhand(rhs w); `65536`] MOD_LT)) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ARITH_TAC]);;
let DB_AND255_NUM = prove
 (`!a. a < 256 ==> word_and (word a) (word 255):int64 = word a`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`a:num`; `0`] DB_AND255_SUB) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; WORD_SUB_0]);;
(* word_zx (word x:M word):N word = word x for x < 65536, M,N among 16,32,64 *)
let DB_ZX_WORD_SMALL = prove
 (`!x. x < 65536 ==>
     word_zx(word x:int16):int32 = word x /\ word_zx(word x:int16):int64 = word x /\
     word_zx(word x:int32):int16 = word x /\ word_zx(word x:int32):int64 = word x /\
     word_zx(word x:int64):int16 = word x /\ word_zx(word x:int64):int32 = word x`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `x < 65536 ==> x < 4294967296 /\ x < 18446744073709551616`]);;
let db_zx_insts x = CONJUNCTS(UNDISCH(SPEC x DB_ZX_WORD_SMALL));;
let DB_AND_WORD_SMALL = prove
 (`!x. x < 65536 ==>
     word_and (word x) (word 65535):int32 = word x /\ word_and (word x) (word 65535):int64 = word x /\
     word_and (word x) (word 65535):int16 = word x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ARITH_RULE `65535 = 2 EXP 16 - 1`; WORD_AND_MASK_WORD] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `x < 65536 ==> x < 4294967296 /\ x < 18446744073709551616`]);;
let db_zx_insts x = CONJUNCTS(UNDISCH(SPEC x DB_ZX_WORD_SMALL)) @ CONJUNCTS(UNDISCH(SPEC x DB_AND_WORD_SMALL));;
let DB_DIV4_BOUND = prove
 (`!c:byte. val c DIV 4 < 64`,
  GEN_TAC THEN SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
  MP_TAC(ISPEC `c:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;
let DB_D_BOUND_TAC : tactic =
  SUBGOAL_THEN `d < 64` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if concl th = `val(EL h (inp:byte list)) DIV 4 = d` then REWRITE_TAC[SYM th] else NO_TAC) THEN
    REWRITE_TAC[DB_DIV4_BOUND]; ALL_TAC];;
let DB_LOWBYTE = prove
 (`!b1 b2. b1 < 256 /\ b2 < 256
     ==> (b1 + 256 * b2) MOD 65536 MOD 256 MOD 4294967296 = b1 MOD 4294967296`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(b1 + 256 * b2) MOD 65536 = b1 + 256 * b2` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(b1 + 256 * b2) MOD 256 = b1` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `b2:num` THEN ASM_ARITH_TAC; REFL_TAC]);;
let DB_MASKS_LOADED = prove
 (`!s pc k. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\ k < 16
     ==> read (memory :> bytes128 (word_add (word pc) (word (31680 + 16 * k)))) s =
         snappy_pattern_mask k 0 /\
         read (memory :> bytes128 (word_add (word pc) (word (31936 + 16 * k)))) s =
         snappy_pattern_mask k 1`,
  let ths = map (fun d -> SNAPPY_IMAGE_CONST_RULE d 128)
              (map (fun k -> 31680 + 16*k) (0--15) @ map (fun k -> 31936 + 16*k) (0--15)) in
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC ths THEN
  REWRITE_TAC[snappy_pattern_mask] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;
let DB_TBL_EXPANDED = EXPAND_SIMD_RULE snappy_tbl;;
let DB_BIT7_SMALL = prove
 (`!n. n < 128 ==> (bit 7 (word_zx (word n:int64):int32) <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_zx (word n:int64):int32 = word n` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT; ARITH_RULE `n < 128 ==> n < 4294967296 /\ n < 18446744073709551616`];
    REWRITE_TAC[BIT_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[DIV_LT; ARITH_ODD]]);;
let DB_COPY_PATTERN_STEP_BYTES = prove
 (`!(m:(S,N word->byte)component) t base out j off q v.
        1 <= off /\ off <= 16 /\ off <= LENGTH out /\
        (!i. i < off
             ==> word_subword q (8 * i,8):byte = EL (LENGTH out - off + i) out) /\
        read (m :> bytelist(base,LENGTH out + 16 * j)) t =
          snappy_copy off (16 * j) out /\
        read (m :> bytes128 (word_add base (word(LENGTH out + 16 * j)))) t = v /\
        (!i. i < 16 ==> word_subword v (8 * i,8):byte = word_subword q (8 * ((16 * j + i) MOD off),8))
        ==> read (m :> bytelist(base,LENGTH out + 16 * j + 16)) t =
            snappy_copy off (16 * j + 16) out`,
  REWRITE_TAC[READ_BYTELIST_EQ_EL; LENGTH_SNAPPY_COPY] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  TRY(CONJ_TAC THENL [ARITH_TAC; ALL_TAC]) THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `i < LENGTH(out:byte list) + 16 * j` THENL
   [FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
       can (find_term ((=) `snappy_copy off (16 * j) (out:byte list)`)) (concl th)
       then MP_TAC(SPEC `i:num` th) else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SNAPPY_COPY_ADD] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC EL_SNAPPY_COPY_PREFIX THEN
    ASM_REWRITE_TAC[LENGTH_SNAPPY_COPY];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) EL_SNAPPY_COPY_PERIODIC o rand o snd) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ABBREV_TAC `u = i - (LENGTH(out:byte list) + 16 * j)` THEN
  SUBGOAL_THEN `i = (LENGTH(out:byte list) + 16 * j) + u /\ u < 16`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  SUBGOAL_THEN `word_add (base:N word) (word((LENGTH(out:byte list) + 16 * j) + u)) =
                word_add (word_add base (word(LENGTH out + 16 * j))) (word u)`
  SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_SIMP_TAC[READ_BYTES8_OF_BYTES128] THEN
  SUBGOAL_THEN `(16 * j + u) MOD off < off` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOD_LT_EQ; ARITH_RULE `1 <= off ==> ~(off = 0)`]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The tag segment.                                                          *)
(* ------------------------------------------------------------------------- *)

let db_find_asm asl t = snd(find (fun (_,th) -> concl th = t) asl);;
let DB_SMALL_FACTS_TAC (ts:term list) : tactic =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [FIRST [MATCH_MP_TAC DB_SX_IWORD_NUM THEN DB_ARITH_TAC THEN NO_TAC;
            MATCH_MP_TAC DB_SX_IWORD_SUB THEN DB_ARITH_TAC THEN NO_TAC;
            MATCH_MP_TAC DB_AND255_NUM THEN DB_ARITH_TAC THEN NO_TAC;
            MATCH_MP_TAC DB_AND255_SUB THEN DB_ARITH_TAC THEN NO_TAC;
            ASM_REWRITE_TAC[DB_AND3; DB_USHR2] THEN NO_TAC]; ALL_TAC]) ts;;

let DB_SUBSUB = WORD_RULE `!x y:int64. word_sub (word_sub x y) x = word_neg y`;;
let DB_SUBSUB2 = WORD_RULE `!x y:int64. word_sub x (word_sub x y) = y`;;
let db_copy_setup typ : tactic =
  let and3 = if typ = 2 then `word_and (word_zx (c:byte)) (word 3):int64 = word 2` else `word_and (word_zx (c:byte)) (word 3):int64 = word 1` in
  let andoff = if typ = 2 then `word_and (word_zx (word off:int16)) (word 65535):int32 = word off`
               else `word_and (word_zx (word v16:int16)) (word 4294902015):int32 = word b1` in
  ABBREV_TAC `d = val(EL h (inp:byte list)) DIV 4` THEN
  ABBREV_TAC `b1 = val(EL (h + 1) (inp:byte list))` THEN
  ABBREV_TAC `b2 = val(EL (h + 2) (inp:byte list))` THEN
  (if typ = 2 then ABBREV_TAC `off = b1 + 256 * b2` else
   ABBREV_TAC `v16 = b1 + 256 * b2` THEN ABBREV_TAC `off = 256 * d DIV 8 + b1`) THEN
  MP_TAC(SPECL [`m:num`; `inp:byte list`; `APPEND ob db:byte list`; `h:num`]
    (if typ = 2 then SNAPPY_TAG_STEP_COPY2_AT else SNAPPY_TAG_STEP_COPY1_AT)) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [DB_ARITH_TAC; ALL_TAC] THEN
  W(fun (asl,_) -> DISCH_THEN(ASSUME_TAC o REWRITE_RULE (mapfilter (db_find_asm asl)
     [`LENGTH (inp:byte list) = li`; `val(EL (h + 1) (inp:byte list)) = b1`; `val(EL (h + 2) (inp:byte list)) = b2`;
      `b1 + 256 * b2 = v16`; `b1 + 256 * b2 = off`; `256 * d DIV 8 + b1 = off`; `val(EL h (inp:byte list)) DIV 4 = d`]))) THEN
  (SUBGOAL_THEN (if typ = 2 then `val(EL h (inp:byte list)) < 256 /\ b1 < 256 /\ b2 < 256 /\ off < 65536 /\ b1 < 65536`
                 else `val(EL h (inp:byte list)) < 256 /\ b1 < 256 /\ b2 < 256 /\ v16 < 65536 /\ off < 65536 /\ b1 < 65536`) STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `EL h (inp:byte list)` VAL_BOUND) THEN MP_TAC(ISPEC `EL (h + 1) (inp:byte list)` VAL_BOUND) THEN
    MP_TAC(ISPEC `EL (h + 2) (inp:byte list)` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
    DB_D_BOUND_TAC THEN ASM_ARITH_TAC; ALL_TAC]) THEN
  DB_D_BOUND_TAC THEN
  (SUBGOAL_THEN `d DIV 8 < 8 /\ d MOD 8 < 8` STRIP_ASSUME_TAC THENL
   [SIMP_TAC[RDIV_LT_EQ; ARITH_EQ; MOD_LT_EQ] THEN DB_ARITH_TAC; ALL_TAC]) THEN
  ABBREV_TAC `c = EL h (inp:byte list)` THEN
  DB_SMALL_FACTS_TAC [and3] THEN
  (SUBGOAL_THEN andoff ASSUME_TAC THENL
   [REWRITE_TAC[DB_AND16_T1; DB_AND16_T2] THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
    REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_16; DIMINDEX_32] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
    FIRST_X_ASSUM(fun th -> if concl th = `b1 + 256 * b2 = v16` || concl th = `b1 + 256 * b2 = off` then REWRITE_TAC[SYM th] else NO_TAC) THEN
    (if typ = 2 then ASM_SIMP_TAC[MOD_LT; ARITH_RULE `b1 < 256 /\ b2 < 256 ==> b1 + 256 * b2 < 65536 /\ b1 + 256 * b2 < 4294967296`]
     else MATCH_MP_TAC DB_LOWBYTE THEN ASM_REWRITE_TAC[]) THEN NO_TAC;
    ALL_TAC]);;
let DB_LEN_TAC : tactic = fun (asl,w) ->
  REWRITE_TAC (LENGTH_APPEND :: mapfilter (db_find_asm asl)
    [`LENGTH (ob:byte list) = op`; `LENGTH (db:byte list) = dl`]) (asl,w);;
let db_reg_value asl s r =
  rhs(concl(snd(find (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s')),_) -> c = r && s' = s
    | _ -> false) asl)));;

(* At the load of the pattern source (ldr q, [x0, x11]): q, the 16 bytes at  *)
(* base + op' - K, and its first K bytes, those of the output.               *)
let DB_SRC_TAC (k:int) (xa:term) (xb:term) : tactic = fun (asl,w) ->
  let s = rand w in
  let av = db_reg_value asl s xa and bv = db_reg_value asl s xb in
  let rd = vsubst [av,`x0:int64`; bv,`x11:int64`; s,`s:armstate`]
             `read (memory :> bytes128 (word_add (x0:int64) (x11:int64))) (s:armstate)` in
  let kt = mk_small_numeral k in
  let addr_eq = mk_eq(vsubst [kt,`k:num`] `word_add base (word ((op + dl) - k)):int64`,
                      vsubst [av,`x0:int64`; bv,`x11:int64`] `word_add (x0:int64) x11`) in
  (X_CHOOSE_TAC `q:int128` (prove(mk_exists(`q:int128`,mk_eq(rd,`q:int128`)),
                                  EXISTS_TAC rd THEN REFL_TAC)) THEN
   MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`; s; `base:int64`;
                  `APPEND ob db:byte list`; kt; `q:int128`] SNAPPY_PATTERN_SOURCE) THEN
   DB_LEN_TAC THEN
   ANTS_TAC THENL
    [REPEAT CONJ_TAC THEN
     FIRST [DB_ARITH_TAC;
            SUBGOAL_THEN addr_eq SUBST1_TAC THENL
             [CONV_TAC(BINOP_CONV DB_NORM_CONV) THEN DB_WORD_EQ_TAC; FIRST_ASSUM ACCEPT_TAC];
            DB_REG_TAC];
     DISCH_TAC]) (asl,w);;

(* The 16 bytes at op' + 16 j, from the stored value (a pattern step).      *)
let DB_PAT_STEP_TAC (k:int) (j:int) (bytes:bool) : tactic = fun (asl,w) ->
  let s = rand w in
  let kt = mk_small_numeral k and jt = mk_small_numeral j in
  if not bytes then
   (MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`; s; `base:int64`;
                   `APPEND ob db:byte list`; jt; kt; `q:int128`] SNAPPY_COPY_PATTERN_STEP) THEN
    DB_LEN_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY DB_ARITH_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      REWRITE_TAC[snappy_copy; ADD_CLAUSES; snappy_pattern_iter; ARITH_RULE `3 = SUC 2 /\ 2 = SUC 1 /\ 1 = SUC 0`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN DB_REG_TAC;
      DISCH_TAC]) (asl,w)
  else
   let km = mk_small_numeral (k - 1) in
   let v = vsubst [km,`kk:num`] `snappy_tbl q (snappy_pattern_mask kk 0)` in
   let c = (16 * j) / k in
   let split = ARITH_RULE(mk_eq(mk_binop `(+):num->num->num` (mk_small_numeral (16 * j)) `i:num`,
                                mk_binop `(+):num->num->num` (mk_binop `( * ):num->num->num` (mk_small_numeral c) kt) `i:num`)) in
   (MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`; s; `base:int64`;
                   `APPEND ob db:byte list`; jt; kt; `q:int128`; v] DB_COPY_PATTERN_STEP_BYTES) THEN
    DB_LEN_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY DB_ARITH_TAC THEN
      REWRITE_TAC[snappy_copy; ADD_CLAUSES] THEN
      FIRST [FIRST_ASSUM ACCEPT_TAC; DB_REG_TAC;
             X_GEN_TAC `i:num` THEN DISCH_TAC THEN
             MP_TAC(SPECL [`q:int128`; kt; `0`; `i:num`] SNAPPY_PATTERN_ITER_BYTE) THEN
             REWRITE_TAC[snappy_pattern_iter] THEN CONV_TAC NUM_REDUCE_CONV THEN
             ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
             DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[split; MOD_MULT_ADD; ADD_CLAUSES] THEN NO_TAC];
      DISCH_TAC]) (asl,w);;

let DB_TRUNC_TAC (k:int) (lent:term) : tactic = fun (asl,w) ->
  let s = rand w in
  (MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`; s; `base:int64`;
                  `APPEND ob db:byte list`; `64`; lent; mk_small_numeral k] SNAPPY_COPY_TRUNC) THEN
   DB_LEN_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
   ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST [DB_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC; DB_REG_TAC]; DISCH_TAC]) (asl,w);;

(* The value of the fact read (memory :> c) t = v whose component is c up to *)
(* the normal form of addresses.                                             *)
let db_mem_value asl t (c:term) =
  let nc = rhs(concl(DB_NORM_CONV c)) in
  rhs(concl(snd(find (fun (_,th) -> db_is_read_fact t th &&
     (let c' = rand(rator(lhs(concl th))) in c' = c ||
      (try rhs(concl(DB_NORM_CONV c')) = nc with Failure _ -> false))) asl)));;

let DB_SUBWORD_ZX_BYTE = prove
 (`!b:byte. word_subword (word_zx b:int128) (0,8):byte = b`, BITBLAST_TAC);;

(* At the ldur of the dup path (offset 1): b, the byte before op'.           *)
let DB_DUP_SRC_TAC : tactic = fun (asl,w) ->
  let s = rand w in
  let av = db_reg_value asl s `X0` in
  let rd = vsubst [av,`x0:int64`; s,`s:armstate`]
             `read (memory :> bytes8 (word_add (x0:int64) (word 18446744073709551615))) (s:armstate)` in
  let addr_eq = mk_eq(`word_add base (word ((op + dl) - 1)):int64`,
                      vsubst [av,`x0:int64`] `word_add (x0:int64) (word 18446744073709551615)`) in
  (X_CHOOSE_TAC `b:byte` (prove(mk_exists(`b:byte`,mk_eq(rd,`b:byte`)),
                                  EXISTS_TAC rd THEN REFL_TAC)) THEN
   SUBGOAL_THEN `!i. i < 1 ==> word_subword (word_zx (b:byte):int128) (8 * i,8):byte =
                 EL ((op + dl) - 1 + i) (APPEND ob db:byte list)` ASSUME_TAC THENL
    [REWRITE_TAC[ARITH_RULE `i < 1 <=> i = 0`] THEN GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; DB_SUBWORD_ZX_BYTE; LENGTH_APPEND] THEN
     DB_LEN_TAC THEN
     MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`; `base:int64`; `op + dl:num`;
                    `(op + dl) - 1`; s] EL_READ_BYTELIST) THEN
     ANTS_TAC THENL [DB_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN (mk_eq(mk_comb(`read (memory :> bytelist(base,op + dl))`,s),`APPEND ob db:byte list`))
       (fun th -> REWRITE_TAC[th]) THENL [DB_REG_TAC; ALL_TAC] THEN
     DISCH_THEN SUBST1_TAC THEN
     SUBGOAL_THEN addr_eq SUBST1_TAC THENL
      [CONV_TAC(BINOP_CONV DB_NORM_CONV) THEN DB_WORD_EQ_TAC;
       FIRST_ASSUM ACCEPT_TAC ORELSE FIRST_ASSUM(ACCEPT_TAC o SYM)];
     ALL_TAC]) (asl,w);;

let DB_DUP_STEP_TAC (j:int) : tactic = fun (asl,w) ->
  let s = rand w in
  let jt = mk_small_numeral j in
  let addr = vsubst [mk_small_numeral (16 * j),`k:num`] `memory :> bytes128 (word_add base (word ((op + dl) + k)))` in
  let v = db_mem_value asl s addr in
  (MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`; s; `base:int64`;
                  `APPEND ob db:byte list`; jt; `1`; `word_zx (b:byte):int128`; v] DB_COPY_PATTERN_STEP_BYTES) THEN
   DB_LEN_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
   ANTS_TAC THENL
    [REPEAT CONJ_TAC THEN TRY DB_ARITH_TAC THEN
     REWRITE_TAC[snappy_copy; ADD_CLAUSES] THEN
     FIRST [FIRST_ASSUM ACCEPT_TAC; DB_REG_TAC;
            REWRITE_TAC[MOD_1; MULT_CLAUSES; DB_SUBWORD_ZX_BYTE] THEN
            CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
            REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST];
     DISCH_TAC]) (asl,w);;

(* read (memory :> c) t = v from a fact whose address is equal to that of c *)
(* by word arithmetic (DB_WORD_EQ_TAC).                                       *)
let db_mem_fact asl t (c:term) : thm =
  let kind,addr = match c with Comb(Comb(Const(":>",_),_),Comb(k,a)) -> k,a | _ -> failwith "db_mem_fact" in
  let try_one (_,th) =
    if not (db_is_read_fact t th) then failwith "" else
    match rand(rator(lhs(concl th))) with
      Comb(Comb(Const(":>",_),_),Comb(k',a')) when k' = kind &&
          set_eq (frees a') (frees addr) && db_maybe_equal a' addr ->
        if a' = addr then th else
        let eq = TAC_PROOF((asl,mk_eq(a',addr)),
                   CONV_TAC(BINOP_CONV DB_NORM_CONV) THEN
                   (REFL_TAC ORELSE (DB_STRIP_ADD_TAC THEN DB_WORD_EQ_TAC))) in
        let lhs_eq = AP_THM (AP_TERM (rator(lhs(concl th)) |> rator) (AP_TERM (rator(rand(rator(lhs(concl th))))) (AP_TERM k' (SYM eq)))) t in
        TRANS lhs_eq th
    | _ -> failwith "" in
  tryfind try_one asl;;

let DB_MEMEQ_TAC : tactic = fun (asl,w) ->
  let t = rand(lhs w) in
  let c1 = rand(rator(lhs w)) and c2 = rand(rator(rhs w)) in
  let th1 = db_mem_fact asl t c1 and th2 = db_mem_fact asl t c2 in
  let v1 = rhs(concl th1) and v2 = rhs(concl th2) in
  if v1 = v2 then (GEN_REWRITE_TAC LAND_CONV [th1] THEN GEN_REWRITE_TAC RAND_CONV [th2] THEN REFL_TAC) (asl,w) else
  let a1 = rand(rand(rand(rator v1))) and a2 = rand(rand(rand(rator v2))) in
  let eq = TAC_PROOF((asl,mk_eq(a1,a2)),
             CONV_TAC(BINOP_CONV DB_NORM_CONV) THEN
             (REFL_TAC ORELSE (DB_STRIP_ADD_TAC THEN DB_WORD_EQ_TAC))) in
  (GEN_REWRITE_TAC LAND_CONV [th1] THEN GEN_REWRITE_TAC RAND_CONV [th2] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ACCEPT_TAC eq) (asl,w);;

let DB_CHUNK_STEP_TAC (j:int) : tactic = fun (asl,w) ->
  let t = rand w in
  (MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`; t; t; `base:int64`;
                  `APPEND ob db:byte list`; mk_small_numeral (16 * j); `16`; `off:num`] SNAPPY_COPY_CHUNK_STEP) THEN
   DB_LEN_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
   ANTS_TAC THENL
    [REPEAT CONJ_TAC THEN TRY DB_ARITH_TAC THEN REWRITE_TAC[snappy_copy; ADD_CLAUSES] THEN

     FIRST [FIRST_ASSUM ACCEPT_TAC;
            MATCH_MP_TAC READ_BYTELIST_OF_BYTES64_PAIR THEN CONJ_TAC THEN DB_MEMEQ_TAC;
            DB_REG_TAC];
     DISCH_TAC]) (asl,w);;

let DB_TRUNCT_TAC (kt:term) (lent:term) : tactic = fun (asl,w) ->
  let s = rand w in
  (MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`; s; `base:int64`;
                  `APPEND ob db:byte list`; `64`; lent; kt] SNAPPY_COPY_TRUNC) THEN
   DB_LEN_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
   ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST [DB_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC; DB_REG_TAC]; DISCH_TAC]) (asl,w);;
let db_tag_leaf extra = db_lemma db_tag_pre (db_tag_bounds ^ " /\\ " ^ extra) "2 * (li - h) + 1";;
let DB_WCASE_TAC (tac:int -> tactic) : tactic =
  SUBGOAL_THEN `w = 1 \/ w = 2` MP_TAC THENL [DB_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2
    (fun th -> SUBST_ALL_TAC th THEN CONV_TAC NUM_REDUCE_CONV THEN
               RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN tac 1)
    (fun th -> SUBST_ALL_TAC th THEN CONV_TAC NUM_REDUCE_CONV THEN
               RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN tac 2));;
let DB_INIT_TAC =
  ENSURES_INIT_TAC "s0" THEN
  REPEAT(FIRST_X_ASSUM(CHOOSE_THEN STRIP_ASSUME_TAC o check (is_exists o concl)));;
let DB_BYTE_TAC (i:term) : tactic =
  MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`; `ip:int64`; `li:num`; i; `s0:armstate`] EL_READ_BYTELIST) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [DB_ARITH_TAC; DISCH_THEN(ASSUME_TAC o SYM)];;
let DB_FLUSH_CALL_TAC (sname:string) : tactic =
  SUBGOAL_THEN `op + 64 <= m` ASSUME_TAC THENL [DB_ARITH_TAC; ALL_TAC] THEN
  ARM_BSTEP_CONTRACT_TAC db_exec DB_FLUSH
   [`read events s`; `base:int64`; `op:num`; `m:num`; `ob:byte list`; `read X1 s`; `dl:num`; `db:byte list`;
    `pc:num`; `rw:num`; `sp:int64`; `read X30 s`; `read X19 s`; `read X20 s`; `read X21 s`; `read X29 s`;
    `ea:int64`; `el:num`; `ev:num`; `ip:int64`; `li:num`] sname;;
let DB_FLUSH_NEXT_TAC : tactic = fun (asl,w) ->
  DB_FLUSH_CALL_TAC ("s" ^ string_of_int (db_state_num w + 1)) (asl,w);;

let db_c1_delta = `word_sub (word_sub (word_sub (word (d MOD 8 + 4)) (word (256 * d DIV 8))) (word b1)) (word (d MOD 8 + 4)):int64 = word_neg (word off)`;;
let db_far_leaf (typ:int) =
  let extra = if typ = 2 then
     "val(EL h inp) MOD 4 = 2 /\\ val(EL h inp) DIV 4 + 1 <= val(EL (h + 1) inp) + 256 * val(EL (h + 2) inp)"
    else "val(EL h inp) MOD 4 = 1 /\\ val(EL h inp) DIV 4 MOD 8 + 4 <= 256 * (val(EL h inp) DIV 4 DIV 8) + val(EL (h + 1) inp)" in
  let lent = if typ = 2 then `d + 1` else `d MOD 8 + 4` in
  let hn = if typ = 2 then `h + 3` else `h + 2` in
  let entry_facts = if typ = 2 then
     [`word_sx(iword(&(d + 1)):int16):int64 = word (d + 1)`; `word_and (word (d + 1)) (word 255):int64 = word (d + 1)`]
    else [`word_sx(iword(&(d MOD 8 + 4) - &(256 * d DIV 8)):int16):int64 = word_sub (word (d MOD 8 + 4)) (word (256 * d DIV 8))`;
          `word_and (word_sub (word (d MOD 8 + 4)) (word (256 * d DIV 8))) (word 255):int64 = word (d MOD 8 + 4)`] in
  let and3 = if typ = 2 then `word_and (word_zx (c:byte)) (word 3):int64 = word 2` else `word_and (word_zx (c:byte)) (word 3):int64 = word 1` in
  let andoff = if typ = 2 then `word_and (word_zx (word off:int16)) (word 65535):int32 = word off`
               else `word_and (word_zx (word v16:int16)) (word 4294902015):int32 = word b1` in
  let small = if typ = 2 then `off:num` else `b1:num` in
  prove(db_tag_leaf extra,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  db_copy_setup typ THEN
  ASM_CASES_TAC `off <= op + dl` THEN
  (fun (asl,w) -> if exists (fun (_,th) -> concl th = `off <= op + dl`) asl then
   (MP_TAC(SPECL [`off:num`; lent; hn] (GENL [`off:num`; `len:num`; `h':num`] (SPEC_ALL DB_STEP_COPY_DEFER))) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE DB_ARITH_TAC); DISCH_TAC]) (asl,w)
   else ALL_TAC (asl,w)) THEN
  DB_SMALL_FACTS_TAC entry_facts THEN
  (if typ = 1 then
     SUBGOAL_THEN db_c1_delta ASSUME_TAC THENL
      [FIRST_X_ASSUM(fun th -> if concl th = `256 * d DIV 8 + b1 = off` then REWRITE_TAC[SYM th] else NO_TAC) THEN
       REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC]
   else ALL_TAC) THEN
  DB_WCASE_TAC (fun wv ->
   W(fun (asl,_) ->
    let rws = [DB_VAL_WORD_ZX_BYTE; DB_AND16_T0; DB_AND16_T1; DB_AND16_T2; WORD_SUB_0] @
      map (db_find_asm asl) (entry_facts @ [and3; andoff] @ (if typ = 1 then [db_c1_delta] else [])) @
      map (PROVE_HYP (db_find_asm asl (mk_binop `(<):num->num->bool` small `65536`))) (db_zx_insts small) in
    DB_INIT_TAC THEN
    MP_TAC(SPECL [`s0:armstate`; `pc:num`; `c:byte`] SNAPPY_LMO_TABLE) THEN
    ASM_REWRITE_TAC[snappy_lmo; GSYM INT_OF_NUM_MUL] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[INT_OF_NUM_MUL] THEN DISCH_TAC THEN
    DB_BYTE_TAC (if typ = 2 then `(h + 1) + 2` else `(h + 1) + 1`) THEN
    MP_TAC(SPECL [`ip:int64`; `inp:byte list`; `li:num`; `h + 1`; `s0:armstate`] DB_BYTES16_EL) THEN
    ASM_REWRITE_TAC[ARITH_RULE `(h + 1) + 1 = h + 2`] THEN ANTS_TAC THENL [DB_ARITH_TAC; DISCH_TAC] THEN
    (fun (asl,w) -> if exists (fun (_,th) -> concl th = `off <= op + dl`) asl then
      (DB_RUN_TAC ~rws [17936] THEN DB_FLUSH_NEXT_TAC THEN DB_RUN_TAC ~rws [25060] THEN
       DB_TO_TAC 1 (mk_binop `(+):num->num->num` (mk_binop `( * ):num->num->num` `2` (mk_binop `(-):num->num->num` `li:num` hn)) `2`)
        [hn; `op + dl:num`; lent; `word_add base (word ((op + dl) - off)):int64`; `APPEND ob db:byte list`;
         mk_icomb(`SUB_LIST:num#num->byte list->byte list`, mk_pair(`(op + dl) - off`,lent)) |> (fun t -> mk_comb(t,`APPEND ob db:byte list`)); `SUC k`; mk_small_numeral wv]) (asl,w)
     else
      (DB_RUN_TAC ~rws [25144] THEN
       DB_TO_TAC 2 `0` [`h:num`; `op:num`; `dl:num`; `dsrc:int64`; `ob:byte list`; `db:byte list`; `k:num`]) (asl,w)))));;
let db_break_leaf (typ:int) =
  let extra = if typ = 0 then "val(EL h inp) MOD 4 = 0 /\\ 60 <= val(EL h inp) DIV 4"
              else "val(EL h inp) MOD 4 = 3" in
  let and3 = if typ = 0 then `word_and (word_zx (c:byte)) (word 3):int64 = word 0`
             else `word_and (word_zx (c:byte)) (word 3):int64 = word 3` in
  prove(db_tag_leaf extra,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `d = val(EL h (inp:byte list)) DIV 4` THEN
  DB_D_BOUND_TAC THEN
  ABBREV_TAC `c = EL h (inp:byte list)` THEN
  SUBGOAL_THEN `val(c:byte) < 256` ASSUME_TAC THENL
   [MP_TAC(ISPEC `c:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC; ALL_TAC] THEN
  (if typ = 0 then SUBGOAL_THEN `~(d < 60)` ASSUME_TAC THENL [DB_ARITH_TAC; ALL_TAC] else ALL_TAC) THEN
  DB_SMALL_FACTS_TAC [`word_sx(iword(&255):int16):int64 = word 255`; and3] THEN
  (if typ = 0 then
     SUBGOAL_THEN `word_ushr (word_zx (c:byte)) 2:int64 = word d /\ word_add (word d) (word 2):int64 = word (d + 2)`
       STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[DB_USHR2; WORD_ADD]; ALL_TAC]
   else ALL_TAC) THEN
  DB_WCASE_TAC (fun wv ->
   W(fun (asl,_) ->
    let rws = [DB_VAL_WORD_ZX_BYTE; DB_AND16_T0; DB_AND16_T1; DB_AND16_T2; WORD_SUB_0; WORD_AND_0] @
      mapfilter (db_find_asm asl) [`word_sx(iword(&255):int16):int64 = word 255`; and3;
        `word_ushr (word_zx (c:byte)) 2:int64 = word d`; `word_add (word d) (word 2):int64 = word (d + 2)`] in
    DB_INIT_TAC THEN
    MP_TAC(SPECL [`s0:armstate`; `pc:num`; `c:byte`] SNAPPY_LMO_TABLE) THEN
    ASM_REWRITE_TAC[snappy_lmo] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
    DB_RUN_TAC ~rws [25144] THEN
    DB_TO_TAC 2 `0` [`h:num`; `op:num`; `dl:num`; `dsrc:int64`; `ob:byte list`; `db:byte list`; `k:num`])));;
let db_offt typ = if typ = 2 then "val(EL (h + 1) (inp:byte list)) + 256 * val(EL (h + 2) (inp:byte list))"
                  else "256 * (val(EL h (inp:byte list)) DIV 4 DIV 8) + val(EL (h + 1) (inp:byte list))";;
let db_lent typ = if typ = 2 then "val(EL h (inp:byte list)) DIV 4 + 1" else "val(EL h (inp:byte list)) DIV 4 MOD 8 + 4";;
let db_near_kind k = if k = 0 then "zero" else if k = 1 then "dup" else if mem k [2;4;8;16] then "single"
                     else if k <= 16 then "chain" else "chunk";;

let db_near_leaf_extra (typ:int) (k:int) =
  Printf.sprintf "val(EL h inp) MOD 4 = %d /\\ %s = %d /\\ %d < %s" typ (db_offt typ) k k (db_lent typ);;

(* The statements of the pattern-copy leaves of typ (1 or 2) for the offsets  *)
(* ks, as one conjunction (the contract of a job).                           *)
let db_near_leaves_stmt (typ:int) (ks:int list) =
  list_mk_conj(map (fun k -> db_tag_leaf (db_near_leaf_extra typ k)) ks);;

let db_near_leaf (typ:int) (k:int) =
  let kt = mk_small_numeral k in
  let extra = db_near_leaf_extra typ k in
  let lent = if typ = 2 then `d + 1` else `d MOD 8 + 4` in
  let hn = if typ = 2 then `h + 3` else `h + 2` in
  let entry_facts = if typ = 2 then
     [`word_sx(iword(&(d + 1)):int16):int64 = word (d + 1)`; `word_and (word (d + 1)) (word 255):int64 = word (d + 1)`]
    else [`word_sx(iword(&(d MOD 8 + 4) - &(256 * d DIV 8)):int16):int64 = word (d MOD 8 + 4)`;
          `word_and (word (d MOD 8 + 4)) (word 255):int64 = word (d MOD 8 + 4)`] in
  let and3 = if typ = 2 then `word_and (word_zx (c:byte)) (word 3):int64 = word 2` else `word_and (word_zx (c:byte)) (word 3):int64 = word 1` in
  let andoff = if typ = 2 then vsubst [kt,`k:num`] `word_and (word_zx (word k:int16)) (word 65535):int32 = word k`
               else vsubst [kt,`k:num`] `word_and (word_zx (word v16:int16)) (word 4294902015):int32 = word k` in
  let kind = db_near_kind k in
  let pc_of off = 24656 + off in
  let stop = if kind = "chain" then [pc_of 0x28c] else if kind = "single" then [pc_of 0x318]
             else if kind = "dup" then [pc_of 0x2f0] else [] in
  let flushed_e = DB_TO_TAC 2 `0` [`h:num`; `op + dl:num`; `0`; db_safe; `APPEND ob db:byte list`; `[]:byte list`; `k:num`] in
  prove(db_tag_leaf extra,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  db_copy_setup typ THEN
  (if typ = 1 then
     SUBGOAL_THEN `d DIV 8 = 0` ASSUME_TAC THENL [DB_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `(b1:num) = off` ASSUME_TAC THENL [DB_ARITH_TAC; ALL_TAC]
   else ALL_TAC) THEN
  (if typ = 1 then
     (SUBGOAL_THEN (hd entry_facts) ASSUME_TAC THENL
       [FIRST_ASSUM(fun th -> if concl th = `d DIV 8 = 0` then REWRITE_TAC[th] else NO_TAC) THEN
        REWRITE_TAC[MULT_CLAUSES; INT_SUB_RZERO] THEN MATCH_MP_TAC DB_SX_IWORD_NUM THEN DB_ARITH_TAC;
        ALL_TAC]) THEN DB_SMALL_FACTS_TAC (tl entry_facts)
   else DB_SMALL_FACTS_TAC entry_facts) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = mk_eq(`off:num`,kt))) THEN
  (if typ = 1 then FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = mk_eq(`b1:num`,kt))) else ALL_TAC) THEN
  MP_TAC(SPEC lent DB_BIT7_SMALL) THEN ANTS_TAC THENL [DB_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPEC_ALL DB_STATIC_FLUSHED) THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE DB_ARITH_TAC); DISCH_TAC] THEN
  ASM_CASES_TAC (vsubst [kt,`k:num`] `k <= op + dl`) THEN
  (fun (asl,w) ->
     let near = k > 0 && exists (fun (_,th) -> concl th = vsubst [kt,`k:num`] `k <= op + dl`) asl in
     ((if near then
       MP_TAC(SPECL [kt; lent; hn] (GENL [`off:num`; `len:num`; `h':num`] (SPEC_ALL DB_STEP_PATTERN))) THEN
       ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE DB_ARITH_TAC); DISCH_TAC]
      else ALL_TAC) THEN
     DB_WCASE_TAC (fun wv ->
      W(fun (asl,_) ->
       let rws = [DB_VAL_WORD_ZX_BYTE; DB_AND16_T0; DB_AND16_T1; DB_AND16_T2; WORD_SUB_0; WORD_AND_0;
                  DB_SUBSUB; DB_SUBSUB2] @
         map (db_find_asm asl) (entry_facts @ [and3; andoff]) @
         map (PROVE_HYP (EQT_ELIM(NUM_REDUCE_CONV(mk_binop `(<):num->num->bool` kt `65536`)))) (db_zx_insts kt) in
       let folds = [DB_TBL_EXPANDED] in
       DB_INIT_TAC THEN
       W(fun (asl,_) ->
       MP_TAC(SPECL [`s0:armstate`; `pc:num`; `c:byte`] SNAPPY_LMO_TABLE) THEN
       REWRITE_TAC(snappy_lmo :: GSYM INT_OF_NUM_MUL :: mapfilter (db_find_asm asl)
         [`aligned_bytes_loaded s0 (word pc) snappy_libsnappy_gcc12_O2_mc`;
          mk_eq(`val(c:byte) MOD 4`, mk_small_numeral typ); `val(c:byte) DIV 4 = d`])) THEN
       CONV_TAC NUM_REDUCE_CONV THEN
       REWRITE_TAC[INT_OF_NUM_MUL] THEN DISCH_TAC THEN
       (if k >= 1 && k <= 16 then
          MP_TAC(SPECL [`s0:armstate`; `pc:num`; mk_small_numeral (k - 1)] DB_MASKS_LOADED) THEN
          ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC
        else ALL_TAC) THEN
       DB_BYTE_TAC (if typ = 2 then `(h + 1) + 2` else `(h + 1) + 1`) THEN
       MP_TAC(SPECL [`ip:int64`; `inp:byte list`; `li:num`; `h + 1`; `s0:armstate`] DB_BYTES16_EL) THEN
       ASM_REWRITE_TAC[ARITH_RULE `(h + 1) + 1 = h + 2`] THEN ANTS_TAC THENL [DB_ARITH_TAC; DISCH_TAC] THEN
       DB_RUN_TAC ~rws ~folds [17936] THEN DB_FLUSH_NEXT_TAC THEN
       (if not near then DB_RUN_TAC ~rws ~folds [25144] THEN flushed_e else
        DB_RUN_TAC ~rws ~folds (stop @ [25060]) THEN
        (if kind = "dup" then DB_DUP_SRC_TAC THEN DB_RUN_TAC ~rws ~folds [25060] else ALL_TAC) THEN
        (if stop <> [] && kind <> "dup" then DB_SRC_TAC k `X0` `X11` THEN DB_RUN_TAC ~rws ~folds [25060] else ALL_TAC) THEN
        (if kind = "chain" then MAP_EVERY (fun j -> DB_PAT_STEP_TAC k j false) (0--3)
         else if kind = "single" then MAP_EVERY (fun j -> DB_PAT_STEP_TAC k j true) (0--3)
         else if kind = "dup" then MAP_EVERY DB_DUP_STEP_TAC (0--3)
         else (fun _ -> failwith ("kind " ^ kind))) THEN
        DB_TRUNC_TAC k lent THEN
        DB_TO_TAC 1 (mk_binop `(+):num->num->num` (mk_binop `( * ):num->num->num` `2` (mk_binop `(-):num->num->num` `li:num` hn)) `2`)
         [hn; vsubst [lent,`len:num`] `op + dl + len:num`; `0`; db_safe;
          mk_comb(mk_comb(mk_comb(`snappy_copy`,kt),lent),`APPEND ob db:byte list`); `[]:byte list`; `SUC k`; mk_small_numeral wv])))) (asl,w)));;
let db_chunk_leaf () =
  let extra = "val(EL h inp) MOD 4 = 2 /\\ 17 <= " ^ db_offt 2 ^ " /\\ " ^ db_offt 2 ^ " < " ^ db_lent 2 in
  let lent = `d + 1` and hn = `h + 3` in
  let entry_facts = [`word_sx(iword(&(d + 1)):int16):int64 = word (d + 1)`; `word_and (word (d + 1)) (word 255):int64 = word (d + 1)`] in
  let and3 = `word_and (word_zx (c:byte)) (word 3):int64 = word 2` in
  let andoff = `word_and (word_zx (word off:int16)) (word 65535):int32 = word off` in
  let flushed_e = DB_TO_TAC 2 `0` [`h:num`; `op + dl:num`; `0`; db_safe; `APPEND ob db:byte list`; `[]:byte list`; `k:num`] in
  prove(db_tag_leaf extra,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  db_copy_setup 2 THEN
  DB_SMALL_FACTS_TAC entry_facts THEN
  MP_TAC(SPEC lent DB_BIT7_SMALL) THEN ANTS_TAC THENL [DB_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPEC_ALL DB_STATIC_FLUSHED) THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE DB_ARITH_TAC); DISCH_TAC] THEN
  ASM_CASES_TAC `off <= op + dl` THEN
  (fun (asl,w) ->
     let near = exists (fun (_,th) -> concl th = `off <= op + dl`) asl in
     ((if near then
       MP_TAC(SPECL [`off:num`; lent; hn] (GENL [`off:num`; `len:num`; `h':num`] (SPEC_ALL DB_STEP_PATTERN))) THEN
       ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE DB_ARITH_TAC); DISCH_TAC]
      else ALL_TAC) THEN
     DB_WCASE_TAC (fun wv ->
      W(fun (asl,_) ->
       let rws = [DB_VAL_WORD_ZX_BYTE; DB_AND16_T0; DB_AND16_T1; DB_AND16_T2; WORD_SUB_0; WORD_AND_0;
                  DB_SUBSUB; DB_SUBSUB2; ADD_ASSUM `LENGTH (db:byte list) = dl` (ADD_ASSUM `LENGTH (ob:byte list) = op` (GSYM(SPECL [`op:num`; `dl:num`] WORD_ADD)))] @
         map (db_find_asm asl) (entry_facts @ [and3; andoff]) @
         map (PROVE_HYP (db_find_asm asl `off < 65536`)) (db_zx_insts `off:num`) in
       DB_INIT_TAC THEN
       MP_TAC(SPECL [`s0:armstate`; `pc:num`; `c:byte`] SNAPPY_LMO_TABLE) THEN
       ASM_REWRITE_TAC[snappy_lmo] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
       DB_BYTE_TAC `(h + 1) + 2` THEN
       MP_TAC(SPECL [`ip:int64`; `inp:byte list`; `li:num`; `h + 1`; `s0:armstate`] DB_BYTES16_EL) THEN
       ASM_REWRITE_TAC[ARITH_RULE `(h + 1) + 1 = h + 2`] THEN ANTS_TAC THENL [DB_ARITH_TAC; DISCH_TAC] THEN
       DB_RUN_TAC ~rws [17936] THEN DB_FLUSH_NEXT_TAC THEN
       (if not near then DB_RUN_TAC ~rws [25144] THEN flushed_e else
        DB_RUN_TAC ~rws [25060] THEN
        MAP_EVERY DB_CHUNK_STEP_TAC (0--3) THEN
        DB_TRUNCT_TAC `off:num` lent THEN
        DB_TO_TAC 1 `2 * (li - (h + 3)) + 2`
         [hn; vsubst [lent,`len:num`] `op + dl + len:num`; `0`; db_safe;
          `snappy_copy off (d + 1) (APPEND ob db)`; `[]:byte list`; `SUC k`; mk_small_numeral wv])))) (asl,w)));;
