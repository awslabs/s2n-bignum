(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* mldsa87_prepare_domain_separation_prefix in the clang 23 build: the proof *)
(* (see prepare_domain_separation_prefix_87_spec.ml). The code has no loop:  *)
(* it checks ctxlen <= 255 and hashalg <= 12, jumps through a table on       *)
(* hashalg to the check of the length of the pre-hash, writes the 2 bytes    *)
(* of the header, copies the context with memcpy, reads the pointer to the   *)
(* OID of entry hashalg - 1 from a table of 12 pointers (relocated by the    *)
(* dynamic loader to the records of rodata_mld_get_hash_oid87_oid_map),      *)
(* copies the OID with an 8-byte store at ctxlen + 2 after a 4-byte store at *)
(* ctxlen + 9 (the two overlap in one byte, with the same value), and copies *)
(* the pre-hash with memcpy. The proof splits the run at the join of the     *)
(* checks (join2, after the jump), and, when both memcpy are called, at the  *)
(* join after the first (join3).                                             *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/prepare_domain_separation_prefix_87_spec.ml";;
needs "x86/proofs/utils/mldsa_native_prefix.ml";;

let MLD_PREFIX87_EXEC =
  MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;

let MLD_PREFIX87_JUMP_TABLE =
  MLD_PREFIX_IMAGE_BYTES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   (layout "mldsa87_prepare_domain_separation_prefix_switch1_table") 52;;

let MLD_PREFIX87_OID_MAP =
  MLD_PREFIX_IMAGE_BYTES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   (layout "rodata_mld_get_hash_oid87_oid_map") 192;;

let MLD_PREFIX87_TEMPLATE =
  let a = "prefix ph phlen ctx ctxlen hashalg mc pc stackpointer returnaddress"
  and h = "val(word_zx hashalg:int32)" in
  let sel f =
    "(" ^ itlist (fun k s -> "if " ^ h ^ " = " ^ string_of_int k ^ " then " ^
                             f ^ string_of_int k ^ " " ^ a ^ " else " ^ s)
                 (1--11) (f ^ "12 " ^ a) ^ ")" in
  parse_term
   ("\\(prefix:int64) (ph:int64) (phlen:num) (ctx:int64) (ctxlen:num) " ^
    "(hashalg:int64) (mc:int64) (pc:num) (stackpointer:int64) " ^
    "(returnaddress:int64). " ^
    "if 255 < ctxlen then f_ev_big " ^ a ^
    " else if " ^ h ^ " = 0 then APPEND (if ctxlen = 0 then f_ev_t00 " ^ a ^
    " else f_ev_t10 " ^ a ^ ") (f_ev_v0 " ^ a ^ ")" ^
    " else if 12 < " ^ h ^ " then f_ev_bad " ^ a ^
    " else if mld_prehash_valid (" ^ h ^ ") phlen then APPEND " ^
    "(if ctxlen = 0 then f_ev_t01 " ^ a ^ " else APPEND (f_ev_tb11 " ^ a ^ ") (f_ev_ta11 " ^ a ^ ")) " ^
    sel "f_ev_v" ^ " else " ^ sel "f_ev_b" ^ ":(uarch_event)list");;

let MLD_PREFIX87_PLT_TAC k =
  LIBC_PLT_TAC MLD_PREFIX87_EXEC (layout "plt_memcpy") (layout "got_memcpy") k;;

let MLD_PREFIX87_MEMCPY_TAC x n =
  LIBC_FULL_CALL_TAC "H_MEMCPY" MLD_PREFIX87_EXEC
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`; x;
    `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   (ref [`prefix:int64`; `ph:int64`; `phlen:num`; `ctx:int64`;
         `ctxlen:num`; `hashalg:int64`; `mc:int64`; `pc:num`;
         `stackpointer:int64`; `returnaddress:int64`]) n;;

let MLD_PREFIX87_INTRO_TAC =
  REPEAT GEN_TAC THEN REWRITE_TAC[memcpy_full_contract] THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC th "H_MEMCPY") THEN
  CONCRETIZE_F_EVENTS_TAC MLD_PREFIX87_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `prefix:int64`; `ph:int64`; `phlen:num`;
    `ctx:int64`; `ctxlen:num`; `hashalg:int64`; `C:num`; `P:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 48 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLD_PREFIX87_EXEC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MLD_PREFIX_VAL_LEN_TAC `prefix:int64` `332` `ctx:int64` `ctxlen:num` THEN
  MLD_PREFIX_VAL_LEN_TAC `prefix:int64` `332` `ph:int64` `phlen:num` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX`;;


let MLD_PREFIX87_FRAME =
 `\s. read RSP s = word_add stackpointer (word 48) /\
      read (memory :> bytes64 (word_add stackpointer (word 48))) s =
      returnaddress /\
      read RBP s = rbp_init /\ read R15 s = r15_init /\
      read R14 s = r14_init /\ read R12 s = r12_init /\
      read RBX s = rbx_init /\
      (read DF s <=> false) /\
      read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
      read (memory :> bytes(ea,el)) s = ev /\
      (!k. k < 12
           ==> read (memory :> bytes64(word(pc + oid_map_ptrs + 8 * k))) s =
               word(pc + rodata_mld_get_hash_oid87_oid_map + 16 * k)) /\
      read (memory :> bytes(ph,phlen)) s = P`;;

let MLD_PREFIX87_APP f x = rhs(concl(BETA_CONV(mk_comb(f,x))));;

let MLD_PREFIX87_STATE extra =
  let s = `s:x86state` in
  mk_abs(s,mk_conj(MLD_PREFIX87_APP extra s,
                   MLD_PREFIX87_APP MLD_PREFIX87_FRAME s));;

let MLD_PREFIX87_MID1 = MLD_PREFIX87_STATE
 `\s. read RDI s = prefix /\ read RSI s = ph /\ read RDX s = word phlen /\
      read RCX s = ctx /\ read RAX s = word ctxlen /\
      read R9 s = (hashalg:int64) /\
      read (memory :> bytes(ctx,ctxlen)) s = C`;;

let MLD_PREFIX87_JUMP_TAC valid k =
  let hk = mk_eq(`val(word_zx (hashalg:int64):int32)`,mk_small_numeral k) in
  let rest = if k = 3 || k = 9 then 12 else 13 in
  REWRITE_TAC[ASSUME hk; ARITH_EQ] THEN
  FULL_INIT_TAC THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (1--2) THEN MLD_PREFIX_BRANCH_TAC THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (3--4) THEN MLD_PREFIX_BRANCH_TAC THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (5--7) THEN MLD_PREFIX_HWORD_TAC k THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV MLD_PREFIX_RIPREL_CONV)) THEN
  MLD_PREFIX_TABLE_TAC MLD_PREFIX87_JUMP_TABLE (4 * k) 4 THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (8--9) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV MLD_PREFIX_PC_CONV)) THEN
  (if k = 0 then X86_STEPS_TAC MLD_PREFIX87_EXEC (10--10) else
   X86_STEPS_TAC MLD_PREFIX87_EXEC (10--12) THEN MLD_PREFIX_BRANCH_TAC THEN
   (if valid then
      (if rest > 12 then X86_STEPS_TAC MLD_PREFIX87_EXEC (13--13) else ALL_TAC)
    else X86_STEPS_TAC MLD_PREFIX87_EXEC (13--22))) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLD_PREFIX87_PURE_MEM_TAC =
  REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[mld_domain_separation_prefix; LENGTH_BYTELIST_OF_NUM;
              num_of_bytelist] THEN
  REWRITE_TAC[MLD_PREFIX_BYTES_COMBINE; MLD_PREFIX_BYTES2] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `ctxlen:num` MLD_PREFIX_VAL_BYTE) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  SUBGOAL_THEN `C < 256 EXP ctxlen` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; GSYM EXP_MULT]; ALL_TAC] THEN
  ASM_SIMP_TAC[NUM_OF_BYTELIST_OF_NUM_EQ; VAL_WORD_0] THEN ARITH_TAC;;

(*** The arithmetic of 1 <= h <= 12 from the case assumptions only, as
     ARITH_RULE with all assumptions fails on the nonlinear ones ***)

let MLD_PREFIX87_H_ARITH_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `mld_prehash_valid (val(word_zx (hashalg:int64):int32)) phlen`
    then MP_TAC(REWRITE_RULE[mld_prehash_valid] th) else NO_TAC) THEN
  ARITH_TAC;;

(*** word_sx of the low half of hashalg, for 1 <= h <= 12, as the simulation
     forms the address of the entry h - 1 of the table of pointers ***)

let MLD_PREFIX_SX_LEMMA = prove
 (`!h. h < 13 ==> 1 <= h
       ==> word(8 * val(word_sx(word h:int32):int64) + 18446744073709551608):int64 =
           word(8 * (h - 1))`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

let MLD_PREFIX87_PTR_TAC n =
  let sn = "s" ^ string_of_int n in
  SUBGOAL_THEN
   `word(8 * val(word_sx(word_zx (hashalg:int64):int32):int64) +
         18446744073709551608):int64 =
    word(8 * (val(word_zx hashalg:int32) - 1))` ASSUME_TAC THENL
   [MP_TAC(SPEC `val(word_zx (hashalg:int64):int32)` MLD_PREFIX_SX_LEMMA) THEN
    REWRITE_TAC[WORD_VAL] THEN
    ANTS_TAC THENL [MLD_PREFIX87_H_ARITH_TAC; ALL_TAC] THEN
    ANTS_TAC THENL [MLD_PREFIX87_H_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   (vsubst [mk_var(sn,`:x86state`),`s:x86state`]
     `read (memory :> bytes64
             (word_add (word(pc + 163312))
                       (word(8 * (val(word_zx (hashalg:int64):int32) - 1))))) s =
      word(pc + rodata_mld_get_hash_oid87_oid_map +
           16 * (val(word_zx hashalg:int32) - 1))`) ASSUME_TAC THENL
   [FIRST_ASSUM(fun th ->
      if is_forall(concl th) && free_in (mk_var(sn,`:x86state`)) (concl th) &&
         can (term_match [] `!k. k < 12 ==> read (memory :> bytes64(word(pc + oid_map_ptrs + 8 * k))) s = x`) (concl th)
      then MP_TAC(SPEC `val(word_zx (hashalg:int64):int32) - 1` th)
      else NO_TAC) THEN
    ANTS_TAC THENL [MLD_PREFIX87_H_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[oid_map_ptrs; GSYM WORD_ADD; ADD_ASSOC] THEN
    DISCH_THEN ACCEPT_TAC;
    ALL_TAC];;

(*** The OID of entry j of the table in the image: its bytes 4 to 11 with an
     8-byte load and its bytes 11 to 14 with a 4-byte one ***)

let MLD_PREFIX87_OID_IMAGE = prove
 (`!(s:x86state) pc.
     bytes_loaded s (word pc)
       mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     ==> !j. j < 12
         ==> read (memory :> bytes64
                    (word_add (word(pc + 153760)) (word (16 * j + 4)))) s =
             word 0x0365014886600906 /\
             read (memory :> bytes32
                    (word_add (word(pc + 153760)) (word ((16 * j + 4) + 7)))) s =
             word (0x20403 + 0x1000000 *
                             val(EL 10 (mld_prehash_oid (j + 1))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY (fun j ->
    MLD_PREFIX_TABLE_TAC MLD_PREFIX87_OID_MAP (16 * j + 4) 8 THEN
    MLD_PREFIX_TABLE_TAC MLD_PREFIX87_OID_MAP (16 * j + 11) 4) (0--11) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[mld_prehash_oid] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let MLD_PREFIX87_ADDR4 = prove
 (`!p k j. word_add (word(p + (k + 16 * j))) (word 4):int64 =
           word_add (word(p + k)) (word (16 * j + 4))`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_RULE);;

let MLD_PREFIX87_ADDR11 = prove
 (`!p k j. word_add (word(p + (k + 16 * j))) (word 11):int64 =
           word_add (word(p + k)) (word ((16 * j + 4) + 7))`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_RULE);;

(*** The facts about the OID of entry hashalg - 1 at the state sN, with the
     addresses as the simulation forms them from RCX ***)

let MLD_PREFIX87_OID_TAC n =
  let sn = mk_var("s" ^ string_of_int n,`:x86state`) in
  MP_TAC(SPECL [sn; `pc:num`] MLD_PREFIX87_OID_IMAGE) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `val(word_zx (hashalg:int64):int32) - 1`) THEN
  ANTS_TAC THENL [MLD_PREFIX87_H_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_zx (hashalg:int64):int32) - 1 + 1 =
                val(word_zx hashalg:int32)` (fun th -> REWRITE_TAC[th]) THENL
   [MLD_PREFIX87_H_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM MLD_PREFIX87_ADDR4; GSYM MLD_PREFIX87_ADDR11] THEN
  STRIP_TAC;;

(*** The prefix of HashML-DSA in memory, in the pieces that the code leaves:
     the 2 bytes of the header, the context, the first 7 bytes of the OID
     (an 8-byte store at ctxlen + 2, whose eighth byte is the 8th, at
     ctxlen + 9, as the 4-byte store at ctxlen + 9 stored the same byte
     first), the last 3 bytes of the 4-byte store and the pre-hash ***)

let MLD_PREFIX87_HASH_SPLIT = prove
 (`!a l n (s:x86state).
        read (memory :> bytes(a,2 + l + 11 + n)) s =
        read (memory :> bytes(a,2)) s +
        2 EXP 16 *
        (read (memory :> bytes(word_add a (word 2),l)) s +
         2 EXP (8 * l) *
         (read (memory :> bytes(word_add a (word (1 * l + 2)),7)) s +
          2 EXP 56 *
          (read (memory :> bytes(word_add a (word (1 * l + 9)),1)) s +
           2 EXP 8 *
           (read (memory :> bytes(word_add a (word (1 * l + 10)),3)) s +
            2 EXP 24 *
            read (memory :> bytes(word_add a (word (1 * l + 13)),n)) s))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 + l + 11 + n = 2 + (l + (7 + (1 + (3 + n))))`] THEN
  REWRITE_TAC[MLD_PREFIX_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; MULT_CLAUSES] THEN
  REWRITE_TAC[ADD_AC] THEN CONV_TAC NUM_REDUCE_CONV);;
let MLD_PREFIX87_D3 = prove
 (`!a (s:x86state) (w:int32).
     read (memory :> bytes32 a) s = w
     ==> read (memory :> bytes(word_add a (word 1),3)) s =
         (val w DIV 256) MOD 2 EXP 24`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[BYTES32_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP (8 * 1)`;
              ARITH_RULE `16777216 = 2 EXP (8 * 3)`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MIN] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let MLD_PREFIX87_TOP1 = prove
 (`!a (s:x86state) (w:int64).
     read (memory :> bytes64 a) s = w
     ==> read (memory :> bytes(word_add a (word 7),1)) s = val w DIV 2 EXP 56`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `72057594037927936 = 2 EXP (8 * 7)`; READ_BYTES_DIV] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(*** The 3 bytes of the 4-byte store at the address A that the 8-byte store
     of bytes 2 to 9 leaves, and the 8th byte of that store (the code stores
     the dword at ctxlen + 9 first), at the state sN after the store ***)

let MLD_PREFIX87_D3_TAC n =
  let sn = mk_var("s" ^ string_of_int n,`:x86state`) in
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),
                          Comb(Comb(Const(":>",_),Const("memory",_)),
                               Comb(Const("bytes32",_),_))),s)),_)
      when s = sn -> ASSUME_TAC(MATCH_MP (SPEC_ALL MLD_PREFIX87_D3) th)
    | _ -> NO_TAC);;

(*** The 8th byte of the 8-byte store to an address involving b ***)

let MLD_PREFIX87_TOP1_TAC b =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),
                          Comb(Comb(Const(":>",_),Const("memory",_)),
                               Comb(Const("bytes64",_),a))),_)),_)
      when free_in b a -> ASSUME_TAC(MATCH_MP (SPEC_ALL MLD_PREFIX87_TOP1) th)
    | _ -> NO_TAC);;

(*** The prefix of HashML-DSA in memory from its pieces: the two bytes of
     the header, the context, the first 7 bytes of the OID, its 8th byte,
     the last 3 bytes of its last 4 and the pre-hash ***)

let MLD_PREFIX87_MEM_LEMMA = prove
 (`!(a:int64) (s:x86state) l phlen h (C:num) (P:num).
     l < 256 /\ 1 <= h /\ h <= 12 /\
     C < 2 EXP (8 * l) /\ P < 2 EXP (8 * phlen) /\
     read (memory :> bytes(a,2)) s = 1 + 256 * l /\
     read (memory :> bytes(word_add a (word 2),l)) s = C /\
     read (memory :> bytes(word_add a (word (1 * l + 2)),7)) s =
       28430383651490054 /\
     read (memory :> bytes(word_add a (word (1 * l + 9)),1)) s = 3 /\
     read (memory :> bytes(word_add a (word (1 * l + 10)),3)) s =
       516 + 65536 * val(EL 10 (mld_prehash_oid h)) /\
     read (memory :> bytes(word_add a (word (1 * l + 13)),phlen)) s = P
     ==> read (memory :> bytes(a,2 + l + 11 + phlen)) s =
         num_of_bytelist
          (mld_domain_separation_prefix h (bytelist_of_num l C)
                                         (bytelist_of_num phlen P))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MLD_PREFIX87_HASH_SPLIT] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(h = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[mld_domain_separation_prefix] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[num_of_bytelist; MLD_PREFIX_NUM_OF_BYTELIST_APPEND;
              LENGTH_BYTELIST_OF_NUM; LENGTH_MLD_PREHASH_OID;
              MLD_PREFIX_OIDN] THEN
  SUBGOAL_THEN `C < 256 EXP l /\ P < 256 EXP phlen` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; GSYM EXP_MULT]; ALL_TAC] THEN
  ASM_SIMP_TAC[NUM_OF_BYTELIST_OF_NUM_EQ] THEN
  SUBGOAL_THEN `val(word l:byte) = l` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_1] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC NUM_RING);;
let MLD_PREFIX87_MEM_LEMMA2 = prove
 (`!(a:int64) (s:x86state) l phlen h (C:num) (P:num).
     l < 256 /\ 1 <= h /\ h <= 12 /\
     C < 2 EXP (8 * l) /\ P < 2 EXP (8 * phlen) /\
     read (memory :> bytes8 a) s = word 1 /\
     read (memory :> bytes8 (word_add a (word 1))) s = word (l MOD 256) /\
     read (memory :> bytes(word_add a (word 2),l)) s = C /\
     read (memory :> bytes(word_add a (word (1 * l + 2)),7)) s =
       28430383651490054 /\
     read (memory :> bytes(word_add (word_add a (word (1 * l + 2))) (word 7),1)) s =
       val(word 244603165765273862:int64) DIV 2 EXP 56 /\
     read (memory :> bytes(word_add (word_add a (word (1 * l + 9))) (word 1),3)) s =
       (val(word(132099 + 16777216 * val(EL 10 (mld_prehash_oid h))):int32) DIV 256)
       MOD 2 EXP 24 /\
     read (memory :> bytes(word_add a (word (l + 13)),phlen)) s = P
     ==> read (memory :> bytes(a,2 + l + 11 + phlen)) s =
         num_of_bytelist
          (mld_domain_separation_prefix h (bytelist_of_num l C)
                                         (bytelist_of_num phlen P))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `s:x86state`; `l:num`; `phlen:num`; `h:num`;
                `C:num`; `P:num`] MLD_PREFIX87_MEM_LEMMA) THEN
  ANTS_TAC THENL
   [ALL_TAC; DISCH_THEN ACCEPT_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `val(EL 10 (mld_prehash_oid h):byte) < 256` ASSUME_TAC THENL
   [MP_TAC(ISPEC `EL 10 (mld_prehash_oid h):byte` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word(132099 + 16777216 * val(EL 10 (mld_prehash_oid h):byte)):int32) =
                132099 + 16777216 * val(EL 10 (mld_prehash_oid h):byte)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_32] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(*** the header ***)
    REWRITE_TAC[MLD_PREFIX_BYTES2] THEN ASM_REWRITE_TAC[VAL_WORD_1] THEN
    MP_TAC(SPEC `l:num` MLD_PREFIX_VAL_BYTE) THEN ANTS_TAC THENL
     [ASM_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[];
    (*** the 8th byte of the OID ***)
    UNDISCH_TAC `read (memory :> bytes(word_add (word_add a (word (1 * l + 2))) (word 7),1)) s =
       val(word 244603165765273862:int64) DIV 2 EXP 56` THEN
    SUBGOAL_THEN `word_add (word_add a (word (1 * l + 2))) (word 7):int64 =
                  word_add a (word (1 * l + 9))` (fun th -> REWRITE_TAC[th]) THENL
     [CONV_TAC WORD_RULE; ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN ACCEPT_TAC;
    (*** the last three bytes ***)
    UNDISCH_TAC `read (memory :> bytes(word_add (word_add a (word (1 * l + 9))) (word 1),3)) s =
       (val(word(132099 + 16777216 * val(EL 10 (mld_prehash_oid h))):int32) DIV 256)
       MOD 2 EXP 24` THEN
    SUBGOAL_THEN `word_add (word_add a (word (1 * l + 9))) (word 1):int64 =
                  word_add a (word (1 * l + 10))` (fun th -> REWRITE_TAC[th]) THENL
     [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(132099 + 16777216 * val(EL 10 (mld_prehash_oid h):byte)) DIV 256 =
                  516 + 65536 * val(EL 10 (mld_prehash_oid h):byte)`
     SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(516 + 65536 * val(EL 10 (mld_prehash_oid h):byte)) MOD 2 EXP 24 =
                  516 + 65536 * val(EL 10 (mld_prehash_oid h):byte)`
     SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN ACCEPT_TAC;
    (*** the pre-hash ***)
    REWRITE_TAC[MULT_CLAUSES] THEN FIRST_ASSUM ACCEPT_TAC]);;

let MLD_PREFIX87_BYTES0 = prove
 (`!a (s:x86state). read (memory :> bytes(a,0)) s = 0`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL]);;

(*** The prefix in memory at the state sN, for a context of ctxlen bytes
     (zero = false) or none (ctxlen replaced by 0 everywhere) ***)

let MLD_PREFIX87_MEM_TAC zero sn =
  let lt = if zero then `0` else `ctxlen:num` in
  let st = mk_var(sn,`:x86state`) in
  DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_PREFIX_ZX_ZX]) THEN
  (if zero then
     SUBGOAL_THEN `C = 0` ASSUME_TAC THENL
      [FIRST_ASSUM(MP_TAC o check (fun th ->
         can (term_match [] `read (memory :> bytes(ctx,0)) s = C`) (concl th))) THEN
       REWRITE_TAC[MLD_PREFIX87_BYTES0] THEN ARITH_TAC; ALL_TAC]
   else ALL_TAC) THEN
  MP_TAC(CONV_RULE(DEPTH_CONV NUM_RED_CONV)
    (SPECL [`prefix:int64`; st; lt; `phlen:num`;
            `val(word_zx (hashalg:int64):int32)`; `C:num`; `P:num`]
           MLD_PREFIX87_MEM_LEMMA2)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST
     [FIRST_ASSUM ACCEPT_TAC;
      MLD_PREFIX87_H_ARITH_TAC;
      (UNDISCH_TAC `~(255 < ctxlen)` THEN ARITH_TAC);
      (REWRITE_TAC[MLD_PREFIX87_BYTES0] THEN ASM_REWRITE_TAC[] THEN NO_TAC);
      (ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN NO_TAC);
      REWRITE_TAC[]];
    DISCH_THEN ACCEPT_TAC];;


let MLD_PREFIX87_FRAME2 =
 `\s. read RSP s = word_add stackpointer (word 8) /\
      read (memory :> bytes64 (word_add stackpointer (word 48))) s =
      returnaddress /\
      read (memory :> bytes64 (word_add stackpointer (word 8))) s = rbx_init /\
      read (memory :> bytes64 (word_add stackpointer (word 16))) s = r12_init /\
      read (memory :> bytes64 (word_add stackpointer (word 24))) s = r14_init /\
      read (memory :> bytes64 (word_add stackpointer (word 32))) s = r15_init /\
      read (memory :> bytes64 (word_add stackpointer (word 40))) s = rbp_init /\
      (read DF s <=> false) /\
      read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
      read (memory :> bytes(ea,el)) s = ev /\
      (!k. k < 12
           ==> read (memory :> bytes64(word(pc + oid_map_ptrs + 8 * k))) s =
               word(pc + rodata_mld_get_hash_oid87_oid_map + 16 * k)) /\
      read (memory :> bytes(ph,phlen)) s = P`;;

let MLD_PREFIX87_MID2 =
  let s = `s:x86state` in
  mk_abs(s,mk_conj(MLD_PREFIX87_APP
   `\s. read RDI s = prefix /\ read RSI s = ph /\ read RDX s = word phlen /\
        read RAX s = word ctxlen /\
        read R9 s = word_zx(word_zx(word_zx(word_zx (hashalg:int64):int32):int64):int32) /\
        read RBX s = prefix /\ read R14 s = ph /\ read R15 s = word phlen /\
        read R12 s = word ctxlen /\ read RBP s = word_zx(word_zx (hashalg:int64):int32) /\
        read (memory :> bytes8 prefix) s = word 1 /\
        read (memory :> bytes8 (word_add prefix (word 1))) s = word(ctxlen MOD 256) /\
        read (memory :> bytes(word_add prefix (word 2),ctxlen)) s = C` s,
   MLD_PREFIX87_APP MLD_PREFIX87_FRAME2 s));;

(*** The call that copies the pre-hash, when the context was copied before:
     its destination is the sum of ctxlen and the prefix, and the
     precondition of memcpy has this address in the form
     word_add (word_add prefix (word ctxlen)) (word 13), for which the
     check of the events needs the equation with the form of the events ***)

let MLD_PREFIX87_MEMCPY2_TAC x n =
  let allowed = ref [`prefix:int64`; `ph:int64`; `phlen:num`; `ctx:int64`;
         `ctxlen:num`; `hashalg:int64`; `mc:int64`; `pc:num`;
         `stackpointer:int64`; `returnaddress:int64`] in
  REMOVE_THEN "H_MEMCPY" (fun th ->
    LIBC_CONTRACT_SIM_TAC ~is_safety_thm:true MLD_PREFIX87_EXEC th
     [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`; x;
      `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`] n THENL
     [(CONJ_TAC THENL [CONV_TAC WORD_RULE; FULL_EXISTS_E2_TAC allowed]) ORELSE
      FULL_EXISTS_E2_TAC allowed;
      LABEL_TAC "H_MEMCPY" th]);;

(*** The events of the paths that read the pointer to the OID: the address
     of the entry is within the table of pointers when hashalg - 1 < 12,
     which CONTAINED_TAC proves after the abbreviation of hashalg - 1. When
     both memcpy are called, the events before join3 are those of the first
     call, which the standard unifier does not associate, so they are
     canonicalized. ***)

let MLD_PREFIX87_SAFETY_H_TAC canon =
  let is_e2_def th =
    let c = concl th in
    is_eq c && is_var(lhs c) && name_of(lhs c) = "e2" in
  let is_e2_meminb th =
    let c = concl th in
    is_comb c &&
    (match strip_comb c with
       Const("memaccess_inbounds",_),(e::_) -> is_var e && name_of e = "e2"
     | _ -> false) in
  RULE_ASSUM_TAC(REWRITE_RULE[oid_map_ptrs]) THEN REWRITE_TAC[oid_map_ptrs] THEN
  SUBGOAL_THEN `val(word_zx (hashalg:int64):int32) - 1 < 12` ASSUME_TAC THENL
   [MLD_PREFIX87_H_ARITH_TAC; ALL_TAC] THEN
  TRY(FIRST_ASSUM(fun dth ->
        if is_e2_def dth then
          FIRST_ASSUM(fun mth ->
            if is_e2_meminb mth then
              STRIP_ASSUME_TAC(REWRITE_RULE[MEMACCESS_INBOUNDS_APPEND]
                                (REWRITE_RULE[dth] mth))
            else NO_TAC)
        else NO_TAC)) THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL
   [(if canon then CANONICALIZE_UNIFY_F_EVENTS_TAC
     else FULL_UNIFY_F_EVENTS_TAC); ALL_TAC] THEN
  REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN
  ABBREV_TAC `j = val(word_zx (hashalg:int64):int32) - 1` THEN
  SUBGOAL_THEN `j < 12` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

(* ------------------------------------------------------------------------- *)
(* The paths of the function, by the cases on ctxlen and hashalg.            *)
(* ------------------------------------------------------------------------- *)

let MLD_PREFIX87_CTX_TOO_LONG_TAC =
  MLD_PREFIX_SELECT_TAC THEN
  REWRITE_TAC[mld_domain_separation_prefix_length] THEN
  ASM_REWRITE_TAC[] THEN
  ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC MLD_PREFIX87_EXEC (1--2) THEN
  MLD_PREFIX_BRANCH_TAC THEN X86_STEPS_TAC MLD_PREFIX87_EXEC (3--12) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLD_PREFIX87_HASH_TOO_BIG_TAC =
  MLD_PREFIX_SELECT_TAC THEN
  REWRITE_TAC[mld_domain_separation_prefix_length; mld_prehash_valid;
              GSYM NOT_LT] THEN
  ASM_REWRITE_TAC[] THEN
  ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC MLD_PREFIX87_EXEC (1--2) THEN
  MLD_PREFIX_BRANCH_TAC THEN X86_STEPS_TAC MLD_PREFIX87_EXEC (3--4) THEN
  MLD_PREFIX_BRANCH_TAC THEN X86_STEPS_TAC MLD_PREFIX87_EXEC (5--14) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** Pure ML-DSA, with an empty context or not, from join2 ***)

let MLD_PREFIX87_PURE_EMPTY_TAC =
  MLD_PREFIX_SELECT_TAC THEN
  REWRITE_TAC[mld_domain_separation_prefix_length] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `ctxlen = 0`)) THEN
  FULL_INIT_TAC THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (1--10) THEN MLD_PREFIX_BRANCH_TAC THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (11--12) THEN MLD_PREFIX_BRANCH_TAC THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (13--26) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES; ARITH_EQ] THEN
  REWRITE_TAC[mld_domain_separation_prefix; LENGTH_BYTELIST_OF_NUM;
              num_of_bytelist; bytelist_of_num; MLD_PREFIX_BYTES2] THEN
  ASM_REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLD_PREFIX87_PURE_CTX_TAC =
  MLD_PREFIX_SELECT_TAC THEN
  REWRITE_TAC[mld_domain_separation_prefix_length] THEN
  ASM_REWRITE_TAC[] THEN
  FULL_INIT_TAC THEN MLD_PREFIX_BOUND_TAC `ctx:int64` THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (1--10) THEN MLD_PREFIX_BRANCH_TAC THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (11--20) THEN
  MLD_PREFIX87_PLT_TAC 20 THEN
  MLD_PREFIX87_MEMCPY_TAC `C:num` 22 THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (23--29) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_PREFIX_ZX_ZX]) THEN
  MLD_PREFIX_BRANCH_TAC THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (30--43) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    MLD_PREFIX87_PURE_MEM_TAC;
    DISCHARGE_SAFETY_PROPERTY_TAC];;

(*** HashML-DSA with an empty context, from join2 ***)

let MLD_PREFIX87_HASH_EMPTY_TAC =
  MLD_PREFIX_SELECT_TAC THEN
  REWRITE_TAC[mld_domain_separation_prefix_length] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `ctxlen = 0`)) THEN
  FULL_INIT_TAC THEN MLD_PREFIX_BOUND_TAC `ph:int64` THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (1--10) THEN MLD_PREFIX_BRANCH_TAC THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (11--12) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_PREFIX_ZX_ZX]) THEN
  MLD_PREFIX_BRANCH_TAC THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (13--14) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV MLD_PREFIX_RIPREL_CONV)) THEN
  MLD_PREFIX87_PTR_TAC 14 THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (15--15) THEN
  MLD_PREFIX87_OID_TAC 15 THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (16--17) THEN
  MLD_PREFIX87_D3_TAC 17 THEN
  MLD_PREFIX87_OID_TAC 17 THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (18--19) THEN
  MLD_PREFIX_LOW7_TAC `prefix:int64` THEN
  MLD_PREFIX87_TOP1_TAC `prefix:int64` THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (20--24) THEN
  MLD_PREFIX87_PLT_TAC 24 THEN
  MLD_PREFIX87_MEMCPY_TAC `P:num` 26 THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (27--42) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    MLD_PREFIX87_MEM_TAC true "s42";
    MLD_PREFIX87_SAFETY_H_TAC false];;

(*** HashML-DSA with a context: the copy of the context, up to join3 ***)

let MLD_PREFIX87_HASH_CTX_A_TAC =
  FULL_INIT_TAC THEN MLD_PREFIX_BOUND_TAC `ctx:int64` THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (1--10) THEN MLD_PREFIX_BRANCH_TAC THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (11--20) THEN
  MLD_PREFIX87_PLT_TAC 20 THEN
  MLD_PREFIX87_MEMCPY_TAC `C:num` 22 THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (23--27) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** and the rest: the OID and the copy of the pre-hash ***)

let MLD_PREFIX87_HASH_CTX_B_TAC =
  FULL_INIT_TAC THEN
  MLD_PREFIX_BOUND_TAC `word_add (prefix:int64) (word 2)` THEN
  MLD_PREFIX_BOUND_TAC `ph:int64` THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (1--2) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_PREFIX_ZX_ZX]) THEN
  MLD_PREFIX_BRANCH_TAC THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (3--4) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_PREFIX_ZX_ZX]) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV MLD_PREFIX_RIPREL_CONV)) THEN
  MLD_PREFIX87_PTR_TAC 4 THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (5--5) THEN
  MLD_PREFIX87_OID_TAC 5 THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (6--7) THEN
  MLD_PREFIX87_D3_TAC 7 THEN
  MLD_PREFIX87_OID_TAC 7 THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (8--9) THEN
  MLD_PREFIX_LOW7_TAC `prefix:int64` THEN
  MLD_PREFIX87_TOP1_TAC `prefix:int64` THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (10--14) THEN
  MLD_PREFIX87_PLT_TAC 14 THEN
  MLD_PREFIX87_MEMCPY2_TAC `P:num` 16 THEN
  X86_STEPS_TAC MLD_PREFIX87_EXEC (17--32) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    MLD_PREFIX87_MEM_TAC false "s32";
    CONV_TAC(DEPTH_CONV MLD_PREFIX_RIPREL_CONV) THEN
    MLD_PREFIX87_SAFETY_H_TAC true];;

let MLD_PREFIX87_HASH_CTX_TAC =
  MLD_PREFIX_SELECT_TAC THEN
  REWRITE_TAC[mld_domain_separation_prefix_length] THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mldsa87_prepare_domain_separation_prefix_join3` MLD_PREFIX87_MID2 THEN
  CONJ_TAC THENL
   [MLD_PREFIX87_HASH_CTX_A_TAC; MLD_PREFIX87_HASH_CTX_B_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety.                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  MLD_PREFIX87_INTRO_TAC THEN
  ASM_CASES_TAC `255 < ctxlen` THENL
   [MLD_PREFIX87_CTX_TOO_LONG_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `val(word_zx (hashalg:int64):int32) = 0` THENL
   [MLD_PREFIX_SELECT_TAC THEN
    ENSURES_EVENTS_SEQUENCE_TAC
     `pc + mldsa87_prepare_domain_separation_prefix_join2` MLD_PREFIX87_MID1 THEN
    CONJ_TAC THENL
     [MLD_PREFIX87_JUMP_TAC true 0;
      ASM_CASES_TAC `ctxlen = 0` THENL
       [MLD_PREFIX87_PURE_EMPTY_TAC; MLD_PREFIX87_PURE_CTX_TAC]];
    ALL_TAC] THEN
  ASM_CASES_TAC `12 < val(word_zx (hashalg:int64):int32)` THENL
   [MLD_PREFIX87_HASH_TOO_BIG_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `mld_prehash_valid (val(word_zx (hashalg:int64):int32)) phlen`
  THENL
   [FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLD_PREFIX_PHLEN_LE) THEN
    MLD_PREFIX_SELECT_TAC THEN
    ENSURES_EVENTS_SEQUENCE_TAC
     `pc + mldsa87_prepare_domain_separation_prefix_join2` MLD_PREFIX87_MID1 THEN
    CONJ_TAC THENL
     [MLD_PREFIX_HCASES_TAC THENL map (MLD_PREFIX87_JUMP_TAC true) (1--12);
      ASM_CASES_TAC `ctxlen = 0` THENL
       [MLD_PREFIX87_HASH_EMPTY_TAC; MLD_PREFIX87_HASH_CTX_TAC]];
    MLD_PREFIX_SELECT_TAC THEN
    REWRITE_TAC[mld_domain_separation_prefix_length] THEN
    ASM_REWRITE_TAC[] THEN
    MLD_PREFIX_HCASES_TAC THENL map (MLD_PREFIX87_JUMP_TAC false) (1--12)]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL)
        th)));;
