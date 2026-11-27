(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The domain separation prefix: the proof (see                              *)
(* prepare_domain_separation_prefix_87_spec.ml).                             *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/prepare_domain_separation_prefix_87_spec.ml";;

let MLD_PREFIX87_EXEC = MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;
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

(* The image bytes are read from an address that is a multiple of 4 *)
let MLD_PREFIX87_JUMP_OFF =
  (layout "mldsa87_prepare_domain_separation_prefix_jump_table") mod 4;;
let MLD_PREFIX87_JUMP_TABLE =
  MLD_PREFIX_IMAGE_BYTES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   ((layout "mldsa87_prepare_domain_separation_prefix_jump_table") -
    MLD_PREFIX87_JUMP_OFF) (13 + MLD_PREFIX87_JUMP_OFF);;
let MLD_PREFIX87_FRAME =
 `\s. read SP s = word_add stackpointer (word 64) /\
      read X30 s = returnaddress /\
      read X19 s = x19_init /\ read X20 s = x20_init /\ read X21 s = x21_init /\
      read X22 s = x22_init /\ read X23 s = x23_init /\
      read (memory :> bytes64(word_add (word pc) (word got_memcpy))) s = mc /\
      read (memory :> bytes(ea,el)) s = ev /\
      (!k. k < 12
           ==> read (memory :> bytes64(word(pc + mldsa87_prepare_domain_separation_prefix_oid_ptrs + 8 * k))) s =
               word(pc + rodata_mld_get_hash_oid87_oid_map + 16 * k)) /\
      read (memory :> bytes(ph,phlen)) s = P`;;
let MLD_PREFIX87_APP f x = rhs(concl(BETA_CONV(mk_comb(f,x))));;
let MLD_PREFIX87_STATE extra =
  let s = `s:armstate` in
  mk_abs(s,mk_conj(MLD_PREFIX87_APP extra s,
                   MLD_PREFIX87_APP MLD_PREFIX87_FRAME s));;
let MLD_PREFIX87_MID1 = MLD_PREFIX87_STATE
 `\s. read X0 s = prefix /\ read X1 s = ph /\ read X2 s = word phlen /\
      read X3 s = ctx /\ read X4 s = word ctxlen /\ read X5 s = hashalg /\
      read (memory :> bytes(ctx,ctxlen)) s = C`;;
let MLD_PREFIX87_HEQ k =
  let hk = mk_eq(`val(word_zx (hashalg:int64):int32)`,mk_small_numeral k) in
  let wth = prove
   (mk_imp(hk,mk_eq(`word_zx (hashalg:int64):int32`,
                    mk_comb(`word:num->int32`,mk_small_numeral k))),
    DISCH_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_32] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV) in
  ASSUME_TAC(UNDISCH wth);;
let PU_CMP12 = prove(`!x:int32. ((&(val x):int) - &12 = &(val(word_sub x (word 12))) /\ ~(val(word_sub x (word 12)) = 0)) <=> 12 < val x`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `x:int32` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  ASM_CASES_TAC `12 <= val(x:int32)` THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN ARITH_TAC;
    ASM_SIMP_TAC[INT_OF_NUM_SUB; ARITH_RULE `~(12 <= x) ==> ~(12 < x)`] THEN
    MATCH_MP_TAC(TAUT `~a ==> ~(a /\ b)`) THEN ONCE_REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN REWRITE_TAC[] THEN INT_ARITH_TAC]);;
let MLD_PREFIX87_JUMP_TAC valid k =
  let hk = mk_eq(`val(word_zx (hashalg:int64):int32)`,mk_small_numeral k) in
  REWRITE_TAC[ASSUME hk; ARITH_EQ] THEN
  FULL_INIT_TAC THEN MLD_PREFIX87_HEQ k THEN
  (if valid then ALL_TAC else
   FIRST_X_ASSUM(fun th ->
     if concl th = `~mld_prehash_valid (val(word_zx (hashalg:int64):int32)) phlen`
     then ASSUME_TAC(REWRITE_RULE[ASSUME hk] th) else NO_TAC)) THEN
  MLD_PREFIX_TABLE_TAC MLD_PREFIX87_JUMP_TABLE (k + MLD_PREFIX87_JUMP_OFF) 1 THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (1--2) THEN MLD_PREFIX_BRANCH_TAC THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (3--4) THEN RULE_ASSUM_TAC(REWRITE_RULE[PU_CMP12]) THEN MLD_PREFIX_BRANCH_TAC THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (5--6) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (7--11) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV MLD_PREFIX_PC_CONV)) THEN
  (if k = 0 then ALL_TAC else
   ARM_STEPS_TAC MLD_PREFIX87_EXEC (12--13) THEN MLD_PREFIX_BRANCH_TAC THEN
   (if valid then
      (if mem k [3;9] then ALL_TAC else ARM_STEPS_TAC MLD_PREFIX87_EXEC (14--14))
    else ARM_STEPS_TAC MLD_PREFIX87_EXEC (14--25))) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let PU_PTRADDR = prove(`!h pc. 1 <= h /\ h <= 12 ==> word_add (word_add (word_add (word pc) (word 327128)) (word_shl (word_sx (word h:int32):int64) 3)) (word 18446744073709551608):int64 = word(pc + (327128 + 8 * (h - 1)))`,
  GEN_TAC THEN GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `h = 1 \/ h = 2 \/ h = 3 \/ h = 4 \/ h = 5 \/ h = 6 \/ h = 7 \/ h = 8 \/ h = 9 \/ h = 10 \/ h = 11 \/ h = 12` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD] THEN (SUBGOAL_THEN `word 18446744073709551608:int64 = word_neg (word 8)` SUBST1_TAC THENL [CONV_TAC WORD_REDUCE_CONV; CONV_TAC WORD_RULE]));;

let MLD_PREFIX87_OID_MAP = MLD_PREFIX_IMAGE_BYTES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc (layout "rodata_mld_get_hash_oid87_oid_map") 192;;

let MLD_PREFIX87_H_ARITH_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `mld_prehash_valid (val(word_zx (hashalg:int64):int32)) phlen`
    then MP_TAC(REWRITE_RULE[mld_prehash_valid] th) else NO_TAC) THEN
  ARITH_TAC;;

(* A byte stored from the low bits of a length register *)
let PU_ZX_ZX_BYTE = prove
 (`!n. word_zx(word_zx(word n:int64):int32):byte = word(n MOD 256)`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPECL [`n:num`; `4294967296`; `4294967296`] MOD_MOD) THEN
  MP_TAC(SPECL [`n:num`; `256`; `16777216`] MOD_MOD) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[MOD_MOD_REFL]);;

let PU_VALBYTE_MOD = prove(`!n. n < 256 ==> val(word(n MOD 256):byte) = n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_8; MOD_MOD_REFL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT]);;

(*** The OID of entry j of the table in the image: its bytes 4 to 11 with an
     8-byte load and its bytes 11 to 14 with a 4-byte one ***)

let MLD_PREFIX87_OID_IMAGE = prove
 (`!(s:armstate) pc.
     aligned_bytes_loaded s (word pc)
       mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     ==> !j. j < 12
         ==> read (memory :> bytes64
                    (word_add (word pc) (word (248620 + 16 * j)))) s =
             word 0x0365014886600906 /\
             read (memory :> bytes32
                    (word_add (word pc) (word (248627 + 16 * j)))) s =
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
 (`!pc j. word_add (word(pc + (rodata_mld_get_hash_oid87_oid_map + 16 * j))) (word 4):int64 =
          word_add (word pc) (word (248620 + 16 * j))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

let MLD_PREFIX87_ADDR11 = prove
 (`!pc j. word_add (word(pc + (rodata_mld_get_hash_oid87_oid_map + 16 * j))) (word 11):int64 =
          word_add (word pc) (word (248627 + 16 * j))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

(*** The facts about the OID of entry hashalg - 1 at the state sN, with the
     addresses as the simulation forms them from RCX ***)

let MLD_PREFIX87_OID_TAC n =
  let sn = mk_var("s" ^ string_of_int n,`:armstate`) in
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
 (`!a l n (s:armstate).
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
 (`!a (s:armstate) (w:int32).
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
 (`!a (s:armstate) (w:int64).
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
  let sn = mk_var("s" ^ string_of_int n,`:armstate`) in
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
 (`!(a:int64) (s:armstate) l phlen h (C:num) (P:num).
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
 (`!(a:int64) (s:armstate) l phlen h (C:num) (P:num).
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
  MP_TAC(SPECL [`a:int64`; `s:armstate`; `l:num`; `phlen:num`; `h:num`;
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
    MP_TAC(SPEC `l:num` PU_VALBYTE_MOD) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
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
 (`!a (s:armstate). read (memory :> bytes(a,0)) s = 0`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL]);;

(*** The prefix in memory at the state sN, for a context of ctxlen bytes
     (zero = false) or none (ctxlen replaced by 0 everywhere) ***)

(* In the path without context, the first byte of the prefix as stored by
   the code: 1, as the hash is not 0 *)
let MLD_PREFIX87_NORM_BYTE0_TAC =
  FIRST_X_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),
                          Comb(Comb(Const(":>",_),Const("memory",_)),
                               Comb(Const("bytes8",_),a))),_)),_)
      when a = `prefix:int64` ->
        ASSUME_TAC(CONV_RULE(RAND_CONV
          (REWRITE_CONV[WORD_SUB_0;
             ASSUME `~(val(word_zx (hashalg:int64):int32) = 0)`] THENC
           WORD_REDUCE_CONV)) th)
    | _ -> NO_TAC);;

let MLD_PREFIX87_MEM_TAC zero sn =
  let lt = if zero then `0` else `ctxlen:num` in
  let st = mk_var(sn,`:armstate`) in
  DISCH_TAC THEN
  (if zero then MLD_PREFIX87_NORM_BYTE0_TAC else ALL_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_PREFIX_ZX_ZX]) THEN
  (if zero then
     SUBGOAL_THEN `C = 0` ASSUME_TAC THENL
      [FIRST_ASSUM(MP_TAC o check (fun th ->
         can (term_match [] `read (memory :> bytes(ctx,0)) s = C`) (concl th))) THEN
       REWRITE_TAC[MLD_PREFIX87_BYTES0] THEN ARITH_TAC; ALL_TAC]
   else ALL_TAC) THEN
  MP_TAC(REWRITE_RULE[MULT_CLAUSES] (CONV_RULE(DEPTH_CONV NUM_RED_CONV)
    (SPECL [`prefix:int64`; st; lt; `phlen:num`;
            `val(word_zx (hashalg:int64):int32)`; `C:num`; `P:num`]
           MLD_PREFIX87_MEM_LEMMA2))) THEN
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



(* The events of the earlier part of the function (the variables f_ev_*
   of the template) may occur in the event list at a call of memcpy. *)
let MLD_PREFIX87_EV_VARS (asl,w) =
  filter (fun v -> let n = name_of v in
                   String.length n > 5 && String.sub n 0 5 = "f_ev_")
         (frees (list_mk_conj (w :: map (concl o snd) asl)));;

let MLD_PREFIX87_ALLOWED =
  [`prefix:int64`; `ph:int64`; `phlen:num`; `ctx:int64`;
   `ctxlen:num`; `hashalg:int64`; `mc:int64`; `pc:num`;
   `stackpointer:int64`; `returnaddress:int64`];;

let MLD_PREFIX87_MEMCPY_TAC x n : tactic =
  fun gl ->
    LIBC_SAFE_CALL_TAC "H_MEMCPY" MLD_PREFIX87_EXEC
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; x;
      `read X30 s`]
     (ref (MLD_PREFIX87_ALLOWED @ MLD_PREFIX87_EV_VARS gl)) n gl;;

let MLD_PREFIX87_PTR_TAC sn =
  let s = mk_var(sn,`:armstate`) in
  let addr = `word_add (word_add (word_add (word pc) (word 327128)) (word_shl (word_sx (word_zx (hashalg:int64):int32):int64) 3)) (word 18446744073709551608):int64` in
  SUBGOAL_THEN (mk_eq(addr,`word(pc + (327128 + 8 * (val(word_zx (hashalg:int64):int32) - 1))):int64`)) ASSUME_TAC THENL
   [MP_TAC(SPECL [`val(word_zx (hashalg:int64):int32)`; `pc:num`] PU_PTRADDR) THEN REWRITE_TAC[WORD_VAL] THEN
    ANTS_TAC THENL [MLD_PREFIX87_H_ARITH_TAC; DISCH_THEN ACCEPT_TAC]; ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
      if is_forall(concl th) && free_in s (concl th) &&
         can (term_match [] `!k. k < 12 ==> read (memory :> bytes64(word(pc + 327128 + 8 * k))) s = x`) (concl th)
      then MP_TAC(SPEC `val(word_zx (hashalg:int64):int32) - 1` th)
      else NO_TAC) THEN
  ANTS_TAC THENL [MLD_PREFIX87_H_ARITH_TAC; ALL_TAC] THEN DISCH_TAC;;

let MLD_PREFIX87_INTRO_TAC =
  REPEAT GEN_TAC THEN REWRITE_TAC[memcpy_full_contract] THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC th "H_MEMCPY") THEN
  CONCRETIZE_F_EVENTS_TAC MLD_PREFIX87_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `prefix:int64`; `ph:int64`; `phlen:num`;
    `ctx:int64`; `ctxlen:num`; `hashalg:int64`; `C:num`; `P:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 64 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLD_PREFIX87_EXEC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
  MLD_PREFIX_VAL_LEN_TAC `prefix:int64` `332` `ctx:int64` `ctxlen:num` THEN
  MLD_PREFIX_VAL_LEN_TAC `prefix:int64` `332` `ph:int64` `phlen:num` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23`;;

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
  SUBGOAL_THEN `val(word_zx (hashalg:int64):int32) - 1 < 12` ASSUME_TAC THENL
   [MLD_PREFIX87_H_ARITH_TAC; ALL_TAC] THEN
  TRY(REWRITE_TAC[ASSUME `word_add (word_add (word_add (word pc) (word 327128)) (word_shl (word_sx (word_zx (hashalg:int64):int32):int64) 3)) (word 18446744073709551608):int64 = word(pc + (327128 + 8 * (val(word_zx hashalg:int32) - 1)))`]) THEN
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


let MLD_PREFIX87_FRAME2 =
 `\s. read SP s = word_add stackpointer (word 16) /\
      read (memory :> bytes64 (word_add stackpointer (word 16))) s = returnaddress /\
      read (memory :> bytes64 (word_add stackpointer (word 24))) s = x23_init /\
      read (memory :> bytes64 (word_add stackpointer (word 32))) s = x22_init /\
      read (memory :> bytes64 (word_add stackpointer (word 40))) s = x21_init /\
      read (memory :> bytes64 (word_add stackpointer (word 48))) s = x20_init /\
      read (memory :> bytes64 (word_add stackpointer (word 56))) s = x19_init /\
      read (memory :> bytes64(word_add (word pc) (word got_memcpy))) s = mc /\
      read (memory :> bytes(ea,el)) s = ev /\
      (!k. k < 12
           ==> read (memory :> bytes64(word(pc + mldsa87_prepare_domain_separation_prefix_oid_ptrs + 8 * k))) s =
               word(pc + rodata_mld_get_hash_oid87_oid_map + 16 * k)) /\
      read (memory :> bytes(ph,phlen)) s = P`;;

let MLD_PREFIX87_APP2 f x = rhs(concl(BETA_CONV(mk_comb(f,x))));;
let MLD_PREFIX87_STATE2 extra =
  let s = `s:armstate` in
  mk_abs(s,mk_conj(MLD_PREFIX87_APP2 extra s,
                   MLD_PREFIX87_APP2 MLD_PREFIX87_FRAME2 s));;
let MLD_PREFIX87_MID2 = MLD_PREFIX87_STATE2
 `\s. read X0 s = prefix /\ read X1 s = ph /\ read X2 s = word phlen /\
      read X4 s = word ctxlen /\
      read X5 s = word_zx(word_zx(word_zx(word_zx (hashalg:int64):int32):int64):int32) /\
      read X19 s = prefix /\ read X20 s = ph /\ read X21 s = word phlen /\
      read X22 s = word ctxlen /\ read X23 s = word_zx(word_zx (hashalg:int64):int32) /\
      read (memory :> bytes8 prefix) s = word 1 /\
      read (memory :> bytes8 (word_add prefix (word 1))) s = word(ctxlen MOD 256) /\
      read (memory :> bytes(word_add prefix (word 2),ctxlen)) s = C`;;

let MLD_PREFIX87_MEMCPY2_TAC x n : tactic =
  fun gl ->
  let allowed = ref (MLD_PREFIX87_ALLOWED @ MLD_PREFIX87_EV_VARS gl) in
  REMOVE_THEN "H_MEMCPY" (fun th ->
    LIBC_CONTRACT_SIM_TAC ~is_safety_thm:true MLD_PREFIX87_EXEC th
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; x;
      `read X30 s`] n THENL
     [(CONJ_TAC THENL [CONV_TAC WORD_RULE; FULL_EXISTS_E2_TAC allowed]) ORELSE
      FULL_EXISTS_E2_TAC allowed;
      LABEL_TAC "H_MEMCPY" th]) gl;;

let MLD_PREFIX87_CTX_TOO_LONG_TAC =
  MLD_PREFIX_SELECT_TAC THEN
  REWRITE_TAC[mld_domain_separation_prefix_length] THEN ASM_REWRITE_TAC[] THEN
  ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC MLD_PREFIX87_EXEC (1--2) THEN
  MLD_PREFIX_BRANCH_TAC THEN ARM_STEPS_TAC MLD_PREFIX87_EXEC (3--14) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLD_PREFIX87_HASH_TOO_BIG_TAC =
  MLD_PREFIX_SELECT_TAC THEN
  REWRITE_TAC[mld_domain_separation_prefix_length; mld_prehash_valid; GSYM NOT_LT] THEN
  ASM_REWRITE_TAC[] THEN
  ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC MLD_PREFIX87_EXEC (1--2) THEN
  MLD_PREFIX_BRANCH_TAC THEN ARM_STEPS_TAC MLD_PREFIX87_EXEC (3--4) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PU_CMP12]) THEN MLD_PREFIX_BRANCH_TAC THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (5--16) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLD_PREFIX87_PURE_EMPTY_TAC =
  MLD_PREFIX_SELECT_TAC THEN
  REWRITE_TAC[mld_domain_separation_prefix_length] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `ctxlen = 0`)) THEN
  FULL_INIT_TAC THEN MLD_PREFIX87_HEQ 0 THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (1--7) THEN MLD_PREFIX_BRANCH_TAC THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (8--9) THEN MLD_PREFIX_BRANCH_TAC THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (10--23) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES; ARITH_EQ] THEN
  REWRITE_TAC[mld_domain_separation_prefix; LENGTH_BYTELIST_OF_NUM;
              num_of_bytelist; bytelist_of_num; MLD_PREFIX_BYTES2] THEN
  ASM_REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES] THEN
  REPEAT CONJ_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLD_PREFIX87_PURE_CTX_TAC =
  MLD_PREFIX_SELECT_TAC THEN
  REWRITE_TAC[mld_domain_separation_prefix_length] THEN ASM_REWRITE_TAC[] THEN
  FULL_INIT_TAC THEN MLD_PREFIX87_HEQ 0 THEN MLD_PREFIX_BOUND_TAC `ctx:int64` THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (1--7) THEN MLD_PREFIX_BRANCH_TAC THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (8--8) THEN MLD_PREFIX_BRANCH_TAC THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (9--17) THEN
  LIBC_PLT_TAC MLD_PREFIX87_EXEC 17 THEN MLD_PREFIX87_MEMCPY_TAC `C:num` 22 THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (23--28) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_PREFIX_ZX_ZX]) THEN MLD_PREFIX_BRANCH_TAC THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (29--42) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FIRST
   [CONV_TAC WORD_RULE THEN NO_TAC;
    MLD_PREFIX87_PURE_MEM_TAC;
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let MLD_PREFIX87_HASH_EMPTY_TAC =
  MLD_PREFIX_SELECT_TAC THEN
  REWRITE_TAC[mld_domain_separation_prefix_length] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `ctxlen = 0`)) THEN
  FULL_INIT_TAC THEN MLD_PREFIX_BOUND_TAC `ph:int64` THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (1--8) THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (9--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_PREFIX_ZX_ZX]) THEN MLD_PREFIX_BRANCH_TAC THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (10--10) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (11--16) THEN
  MLD_PREFIX87_PTR_TAC "s16" THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (17--17) THEN MLD_PREFIX87_OID_TAC 17 THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (18--18) THEN MLD_PREFIX87_OID_TAC 18 THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (19--20) THEN MLD_PREFIX87_D3_TAC 20 THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (21--21) THEN
  MLD_PREFIX_LOW7_TAC `prefix:int64` THEN MLD_PREFIX87_TOP1_TAC `prefix:int64` THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (22--22) THEN LIBC_PLT_TAC MLD_PREFIX87_EXEC 22 THEN
  MLD_PREFIX87_MEMCPY_TAC `P:num` 27 THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (28--43) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FIRST
   [CONV_TAC WORD_RULE THEN NO_TAC;
    MLD_PREFIX87_MEM_TAC true "s43";
    MLD_PREFIX87_SAFETY_H_TAC false];;

let MLD_PREFIX87_HASH_CTX_A_TAC =
  FULL_INIT_TAC THEN MLD_PREFIX_BOUND_TAC `ctx:int64` THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (1--8) THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (9--17) THEN
  LIBC_PLT_TAC MLD_PREFIX87_EXEC 17 THEN MLD_PREFIX87_MEMCPY_TAC `C:num` 22 THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (23--27) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[WORD_SUB_0] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[PU_ZX_ZX_BYTE]; DISCHARGE_SAFETY_PROPERTY_TAC];;

let MLD_PREFIX87_HASH_CTX_B_TAC =
  FULL_INIT_TAC THEN
  MLD_PREFIX_BOUND_TAC `word_add (prefix:int64) (word 2)` THEN
  MLD_PREFIX_BOUND_TAC `ph:int64` THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (1--1) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_PREFIX_ZX_ZX]) THEN MLD_PREFIX_BRANCH_TAC THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (2--2) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (3--8) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_PREFIX_ZX_ZX]) THEN
  MLD_PREFIX87_PTR_TAC "s8" THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (9--9) THEN MLD_PREFIX87_OID_TAC 9 THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (10--10) THEN MLD_PREFIX87_OID_TAC 10 THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (11--12) THEN MLD_PREFIX87_D3_TAC 12 THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (13--13) THEN
  MLD_PREFIX_LOW7_TAC `prefix:int64` THEN MLD_PREFIX87_TOP1_TAC `prefix:int64` THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (14--14) THEN LIBC_PLT_TAC MLD_PREFIX87_EXEC 14 THEN
  MLD_PREFIX87_MEMCPY2_TAC `P:num` 19 THEN
  ARM_STEPS_TAC MLD_PREFIX87_EXEC (20--35) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FIRST
   [CONV_TAC WORD_RULE THEN NO_TAC;
    MLD_PREFIX87_MEM_TAC false "s35";
    MLD_PREFIX87_SAFETY_H_TAC true];;

let MLD_PREFIX87_HASH_CTX_TAC =
  MLD_PREFIX_SELECT_TAC THEN
  REWRITE_TAC[mld_domain_separation_prefix_length] THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mldsa87_prepare_domain_separation_prefix_join3` MLD_PREFIX87_MID2 THEN
  CONJ_TAC THENL [MLD_PREFIX87_HASH_CTX_A_TAC; MLD_PREFIX87_HASH_CTX_B_TAC];;

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
    REWRITE_TAC[mld_domain_separation_prefix_length] THEN ASM_REWRITE_TAC[] THEN
    MLD_PREFIX_HCASES_TAC THENL map (MLD_PREFIX87_JUMP_TAC false) (1--12)]);;

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
