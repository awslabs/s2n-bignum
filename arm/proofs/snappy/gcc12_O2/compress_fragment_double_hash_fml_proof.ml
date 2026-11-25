(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The five copies of FindMatchLengthPlain in CompressFragmentDoubleHash     *)
(* (compress_fragment_double_hash_fml_spec.ml). Each copy is proved in       *)
(* parts, from the points of its code:                                       *)
(*                                                                           *)
(*   the byte loop (for b + j < LENGTH src: the bytes at a + j and b + j),   *)
(*   the start of the byte loop (b + j > LENGTH src - 8),                    *)
(*   the loop of 8-byte comparisons (b + 8 j + 8 <= LENGTH src; a           *)
(*   difference ends it with the lowest set bit of the exclusive or,         *)
(*   SNAPPY_MATCH_LENGTH_NE8),                                               *)
(*   the start (the contract),                                               *)
(*                                                                           *)
(* each with j bytes known to match:                                         *)
(*   snappy_match_length src a b = j + snappy_match_length src (a+j) (b+j). *)
(* The loops are by well-founded induction on LENGTH src - (b + j), the      *)
(* step that goes round the loop going through the induction hypothesis     *)
(* (FML_CALL_TAC), as the other parts go through the parts they reach.       *)
(* The copies A, B, D and E have the same shape (fml_copy_lemmas); C has     *)
(* its index in a register of its own.                                       *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_fml_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_lib.ml";;

(* ------------------------------------------------------------------------- *)
(* Facts about match lengths.                                                *)
(* ------------------------------------------------------------------------- *)

let FML_MATCH_LENGTH_STEP = prove
 (`!(src:byte list) a b.
     b < LENGTH src
     ==> snappy_match_length src a b =
         if EL a src = EL b src
         then snappy_match_length src (a + 1) (b + 1) + 1 else 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[snappy_match_length] THEN
  SUBGOAL_THEN `LENGTH(src:byte list) - b = SUC(LENGTH src - (b + 1))`
   SUBST1_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[snappy_mlen; ADD1]]);;

let FML_MATCH_LENGTH_END = prove
 (`!(src:byte list) a b.
     LENGTH src <= b ==> snappy_match_length src a b = 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[snappy_match_length] THEN
  SUBGOAL_THEN `LENGTH(src:byte list) - b = 0` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[snappy_mlen]]);;

(* The first difference of two 8-byte loads from the lowest set bit of     *)
(* their exclusive or.                                                     *)

let SNAPPY_MATCH_LENGTH_NE8 = prove
 (`!(src:byte list) a b.
     a + 8 <= LENGTH src /\ b + 8 <= LENGTH src /\
     ~(snappy_load64 src a = snappy_load64 src b)
     ==> snappy_match_length src a b =
         word_ctz(word_xor (word(snappy_load64 src a))
                           (word(snappy_load64 src b)):int64) DIV 8 /\
         snappy_match_length src a b < 8`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?m. m < 8 /\ ~(EL (a + m) src = EL (b + m) (src:byte list)) /\
        !i. i < m ==> EL (a + i) src = EL (b + i) src`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    ASM_SIMP_TAC[SNAPPY_LOAD64_EQ_BYTES] THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
    GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `i < 8` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `snappy_match_length src a b = m` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`m:num`; `src:byte list`; `a:num`; `b:num`;
                   `LENGTH(src:byte list) - (b + m)`] SNAPPY_MLEN_SHIFT) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `m + (LENGTH(src:byte list) - (b + m)) = LENGTH src - b`
     SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM snappy_match_length] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`src:byte list`; `a + m`; `b + m`] FML_MATCH_LENGTH_STEP) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `z = word_ctz(word_xor (word(snappy_load64 src a))
                                    (word(snappy_load64 src b)):int64)` THEN
  SUBGOAL_THEN `8 * m <= z` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN
    REWRITE_TAC[WORD_LE_CTZ_VAL_MOD; SNAPPY_XOR_MOD_EQ_0; DIMINDEX_64;
                VAL_WORD] THEN
    SIMP_TAC[MOD_LT; SNAPPY_LOAD64_BOUND] THEN
    REWRITE_TAC[SNAPPY_MOD_BYTES_EQ] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`src:byte list`; `a:num`; `i:num`] SNAPPY_LOAD64_BYTE) THEN
    MP_TAC(ISPECL [`src:byte list`; `b:num`; `i:num`] SNAPPY_LOAD64_BYTE) THEN
    REPEAT(ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(8 * (m + 1) <= z)` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN
    REWRITE_TAC[WORD_LE_CTZ_VAL_MOD; SNAPPY_XOR_MOD_EQ_0; DIMINDEX_64;
                VAL_WORD] THEN
    SIMP_TAC[MOD_LT; SNAPPY_LOAD64_BOUND] THEN
    REWRITE_TAC[SNAPPY_MOD_BYTES_EQ; DE_MORGAN_THM] THEN DISJ2_TAC THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN EXISTS_TAC `m:num` THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`src:byte list`; `a:num`; `m:num`] SNAPPY_LOAD64_BYTE) THEN
    MP_TAC(ISPECL [`src:byte list`; `b:num`; `m:num`] SNAPPY_LOAD64_BYTE) THEN
    REPEAT(ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC]) THEN
    ASM_REWRITE_TAC[VAL_EQ];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC DIV_UNIQ THEN
  EXISTS_TAC `z - 8 * m` THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The byte loop, the start of the byte loop and the loop of 8-byte         *)
(* comparisons of the copies A, B, D and E, from their parameters.           *)
(* ------------------------------------------------------------------------- *)

let fml_stmt (pre:string) (post:string) (frame:string) (extra:string) =
  parse_term
   ("!src inp a b j pc e. " ^ snappy_cf2_fml_hyps ^ " /\\ " ^ extra ^ "
     ==> ensures arm
          (\\s. " ^ snappy_cf2_fml_pre ^ " /\\ " ^ pre ^ ")
          (\\s. " ^ post ^ " /\\ " ^ snappy_cf2_fml_ev ^ ")
          (" ^ frame ^ ")");;

(* post: the postcondition (with a b); s1: the register with inp + a; lim:  *)
(* the register with LENGTH src - b in the byte loop; ne6: the byte loop    *)
(* exits on a difference with one more step (b join3 of copy A); tail_n:    *)
(* the last step of the start of the byte loop.                             *)

type fml_copy =
  { post : string; frame : string; s1 : string; lim : string;
    byte_pc : int; ne6 : bool; tail_pc : int; tail_n : int;
    loop_pc : int; ne_cond : term };;

let fml_x16 = "read X16 s = word_add inp (word(LENGTH src - 8))";;

let fml_byte_stmt (p:fml_copy) =
  fml_stmt
   ("read PC s = word(pc + " ^ string_of_int p.byte_pc ^ ") /\\
     read " ^ p.s1 ^ " s = word_add inp (word a) /\\
     read X6 s = word_add inp (word b) /\\ " ^ fml_x16 ^ " /\\
     read " ^ p.lim ^ " s = word(LENGTH src - b) /\\
     read X4 s = word j")
   p.post p.frame
   "a < b /\\ b + j < LENGTH src /\\
    snappy_match_length src a b = j + snappy_match_length src (a + j) (b + j)";;

let FML_BYTE_TAC (p:fml_copy) =
  FML_INDUCT_TAC `LENGTH(src:byte list) - (b + j)` THEN
  STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  FML_READ8_TAC `word_add (word_add (inp:int64) (word a)) (word j)` `a + j` THEN
  FML_READ8_TAC `word_add (word_add (inp:int64) (word b)) (word j)` `b + j` THEN
  ARM_BSTEP_TAC FML_EXEC (1--5) THEN
  FML_FACT_TAC FML_MATCH_LENGTH_STEP [`src:byte list`; `a + j`; `b + j`] THEN
  FML_BRANCH_TAC ~tac:FML_BYTE_EQ_TAC
    `EL (a + j) (src:byte list) = EL (b + j) src` THENL
   [ARM_BSTEP_TAC FML_EXEC (6--8) THEN
    FML_BRANCH_TAC `b + j + 1 = LENGTH(src:byte list)` THENL
     [ARM_BSTEP_TAC FML_EXEC (9--10) THEN
      FML_FACT_TAC FML_MATCH_LENGTH_END
        [`src:byte list`; `a + j + 1`; `b + j + 1`] THEN
      FML_FIN_TAC THEN FML_REG_TAC;
      FML_CANON_TAC "X4" `word(j + 1):int64` THEN
      FML_IH_TAC [`j + 1`,"j"] "s9" THEN
      FML_FIN_TAC];
    (if p.ne6 then ARM_BSTEP_TAC FML_EXEC (6--6) else ALL_TAC) THEN
    FML_FIN_TAC THEN FML_REG_TAC];;

let fml_tail_stmt (p:fml_copy) =
  fml_stmt
   ("read PC s = word(pc + " ^ string_of_int p.tail_pc ^ ") /\\
     read " ^ p.s1 ^ " s = word_add inp (word a) /\\
     read X6 s = word_add inp (word(b + j)) /\\ " ^ fml_x16 ^ " /\\
     read X4 s = word j")
   p.post p.frame
   "a < b /\\ b + j <= LENGTH src /\\
    snappy_match_length src a b = j + snappy_match_length src (a + j) (b + j)";;

let FML_TAIL_TAC (p:fml_copy) (byte:thm) =
  let sn = "s" ^ string_of_int(p.tail_n + 1) in
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ARM_BSTEP_TAC FML_EXEC (1--2) THEN
  FML_BRANCH_TAC `LENGTH(src:byte list) <= b + j` THENL
   [FML_FACT_TAC FML_MATCH_LENGTH_END [`src:byte list`; `a + j`; `b + j`] THEN
    FML_FIN_TAC THEN FML_REG_TAC;
    ARM_BSTEP_TAC FML_EXEC (3--p.tail_n) THEN
    FML_CANON_TAC "X4" `word j:int64` THEN
    FML_CANON_TAC "X6" `word_add inp (word b):int64` THEN
    FML_CANON_TAC p.lim `word(LENGTH(src:byte list) - b):int64` THEN
    FML_CALL_TAC byte [] sn THEN
    FML_FIN_TAC];;

let fml_loop_stmt (p:fml_copy) =
  fml_stmt
   ("read PC s = word(pc + " ^ string_of_int p.loop_pc ^ ") /\\
     read X6 s = word_add inp (word(b + 8 * j)) /\\
     read X7 s = word_add inp (word(a + 8 * j)) /\\
     read " ^ p.s1 ^ " s = word_add inp (word a) /\\ " ^ fml_x16 ^ " /\\
     read X4 s = word(8 * j)")
   p.post p.frame
   "a < b /\\ b + 8 * j + 8 <= LENGTH src /\\
    snappy_match_length src a b =
    8 * j + snappy_match_length src (a + 8 * j) (b + 8 * j)";;

(* The register c (goal read c s = word(snappy_match_length src a b)) after *)
(* the ctz exit: its value 32-bit k + (clz(rbit(x xor y)) >> 3).            *)

let FML_CTZ_TAC : tactic =
  W(fun (asl,w) ->
    let l,_ = dest_eq w in
    let th = snd(find (fun (_,th) -> is_eq(concl th) && lhs(concl th) = l) asl) in
    GEN_REWRITE_TAC LAND_CONV [th]) THEN
  REWRITE_TAC[WORD_CLZ_REVERSEFIELDS] THEN
  W(fun (asl,w) ->
    let z = find_term (fun t -> match t with
        Comb(Const("word_ctz",_),_) -> true | _ -> false) w in
    let zlt = mk_binary "<" (z,`64`) in
    let zth = TAC_PROOF((asl,zlt),
      SUBGOAL_THEN (mk_binary "<" (mk_binary "DIV" (z,`8`),`8`)) MP_TAC THENL
       [CF2_ARITH_TAC; SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ARITH_TAC]) in
    let eqth = snd(find (fun (_,th) -> is_eq(concl th) &&
                         rhs(concl th) = mk_binary "DIV" (z,`8`)) asl) in
    ASSUME_TAC zth THEN REWRITE_TAC[MATCH_MP FML_CTZ_ISHR3 zth; GSYM eqth]) THEN
  FML_WORD_EQ_TAC;;

let FML_LOOP_TAC (p:fml_copy) (tail:thm) =
  FML_INDUCT_TAC `LENGTH(src:byte list) - (b + 8 * j)` THEN
  STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  FML_READ64_TAC `word_add (inp:int64) (word(a + 8 * j))` `a + 8 * j` THEN
  FML_READ64_TAC `word_add (inp:int64) (word(b + 8 * j))` `b + 8 * j` THEN
  ARM_BSTEP_TAC FML_EXEC (1--5) THEN
  FML_BRANCH_TAC
   `snappy_load64 src (a + 8 * j) = snappy_load64 src (b + 8 * j)` THENL
   [FML_FACT_TAC SNAPPY_MATCH_LENGTH_EQ8
      [`src:byte list`; `a + 8 * j`; `b + 8 * j`] THEN
    ARM_BSTEP_TAC FML_EXEC (6--9) THEN
    FML_BRANCH_TAC `LENGTH(src:byte list) - 8 < b + 8 * j + 8` THENL
     [FML_CANON_TAC "X6" `word_add inp (word(b + 8 * j + 8)):int64` THEN
      FML_CANON_TAC "X4" `word(8 * j + 8):int64` THEN
      FML_CALL_TAC tail [`8 * j + 8`,"j"] "s10" THEN FML_FIN_TAC;
      FML_CANON_TAC "X6" `word_add inp (word(b + 8 * (j + 1))):int64` THEN
      FML_CANON_TAC "X7" `word_add inp (word(a + 8 * (j + 1))):int64` THEN
      FML_CANON_TAC "X4" `word(8 * (j + 1)):int64` THEN
      FML_IH_TAC [`j + 1`,"j"] "s10" THEN FML_FIN_TAC];
    FML_FACT_TAC SNAPPY_MATCH_LENGTH_NE8
      [`src:byte list`; `a + 8 * j`; `b + 8 * j`] THEN
    ARM_BSTEP_TAC FML_EXEC (6--7) THEN
    FML_KNOWN_BRANCH_TAC p.ne_cond THEN
    FML_READ64_TAC
     `word_add (word_add (inp:int64) (word a))
               (word_sx (word_zx (word (8 * j):int64):int32))`
     `a + 8 * j` THEN
    ARM_BSTEP_TAC FML_EXEC (8--13) THEN
    FML_FIN_TAC THEN FML_CTZ_TAC];;

let fml_copy_lemmas (p:fml_copy) =
  let byte = prove(fml_byte_stmt p,FML_BYTE_TAC p) in
  let tail = prove(fml_tail_stmt p,FML_TAIL_TAC p byte) in
  let loop = prove(fml_loop_stmt p,FML_LOOP_TAC p tail) in
  byte,tail,loop;;

(* ------------------------------------------------------------------------- *)
(* The copies A, B, D and E.                                                 *)
(* ------------------------------------------------------------------------- *)

let fml_ml_post lbl reg x16 =
  "read PC s = word(pc + " ^ lbl ^ ") /\\ " ^
  (if x16 then fml_x16 ^ " /\\ " else "") ^
  "read " ^ reg ^ " s = word(snappy_match_length src a b)";;

let fml_a_copy =
  { post = fml_ml_post "CompressFragmentDoubleHash_join3" "X4" true;
    frame = "MAYCHANGE [PC; X4; X6; X7; X15; X16; X17; X18; X19] ,,
             MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events]";
    s1 = "X18"; lim = "X17"; byte_pc = 16744; ne6 = true;
    tail_pc = 16704; tail_n = 7; loop_pc = 15360;
    ne_cond = `LENGTH(src:byte list) - 8 < b + 8 * j` };;

let fml_b_copy =
  { post = fml_ml_post "CompressFragmentDoubleHash_join9" "X4" false;
    frame = "MAYCHANGE [PC; X4; X6; X7; X17; X18; X19; X20] ,,
             MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events]";
    s1 = "X19"; lim = "X18"; byte_pc = 16824; ne6 = false;
    tail_pc = 16800; tail_n = 6; loop_pc = 15692;
    ne_cond = `LENGTH(src:byte list) - 8 < b + 8 * j` };;

let fml_de_frame =
  "MAYCHANGE [PC; X4; X6; X7; X8; X15; X17; X18] ,,
   MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events]";;

let fml_d_copy =
  { post = fml_ml_post "CompressFragmentDoubleHash_join18" "X4" false;
    frame = fml_de_frame;
    s1 = "X17"; lim = "X15"; byte_pc = 16280; ne6 = false;
    tail_pc = 16256; tail_n = 6; loop_pc = 16228;
    ne_cond = `b + 8 * j <= LENGTH(src:byte list) - 8` };;

let fml_e_copy =
  { post = fml_ml_post "CompressFragmentDoubleHash_join18" "X4" false;
    frame = fml_de_frame;
    s1 = "X17"; lim = "X15"; byte_pc = 17048; ne6 = false;
    tail_pc = 17024; tail_n = 6; loop_pc = 16552;
    ne_cond = `LENGTH(src:byte list) - 8 < b + 8 * j` };;

(* The start of a copy: steps 1..k to the test b + 8 > LENGTH src - 8, then *)
(* the steps to the start of the byte loop (taken) or to the loop.          *)

let FML_MAIN_TAC (tail:thm) (loop:thm) (k:int) (canon:tactic) (nt:int) (nl:int) =
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ARM_BSTEP_TAC FML_EXEC (1--k) THEN canon THEN
  FML_BRANCH_TAC `LENGTH(src:byte list) - 8 < ip + 4` THENL
   [ARM_BSTEP_TAC FML_EXEC ((k+1)--(k+nt)) THEN canon THEN
    FML_CALL_TAC tail [`c + 4`,"a"; `ip + 4`,"b"; `0`,"j"]
      ("s" ^ string_of_int(k+nt+1)) THEN
    FML_FIN_TAC;
    ARM_BSTEP_TAC FML_EXEC ((k+1)--(k+nl)) THEN canon THEN
    FML_CALL_TAC loop [`c + 4`,"a"; `ip + 4`,"b"; `0`,"j"]
      ("s" ^ string_of_int(k+nl+1)) THEN
    FML_FIN_TAC];;

let FML_CANONS_TAC (l:(string*term) list) =
  MAP_EVERY (fun (c,t) -> TRY(FML_CANON_TAC c t)) l;;

let fml_a_byte,fml_a_tail,fml_a_loop = fml_copy_lemmas fml_a_copy;;

let SNAPPY_CF2_GCC12_O2_FML_A = prove
 (SNAPPY_CF2_GCC12_O2_FML_A_STMT,
  FML_MAIN_TAC fml_a_tail fml_a_loop 5
   (FML_CANONS_TAC
     ["X16",`word_add inp (word(LENGTH(src:byte list) - 8)):int64`;
      "X6",`word_add inp (word(ip + 4)):int64`;
      "X18",`word_add inp (word(c + 4)):int64`;
      "X7",`word_add inp (word(c + 4)):int64`]) 1 3);;

let fml_b_byte,fml_b_tail,fml_b_loop = fml_copy_lemmas fml_b_copy;;

let SNAPPY_CF2_GCC12_O2_FML_B = prove
 (SNAPPY_CF2_GCC12_O2_FML_B_STMT,
  FML_MAIN_TAC fml_b_tail fml_b_loop 3
   (FML_CANONS_TAC
     ["X19",`word_add inp (word(c + 4)):int64`;
      "X7",`word_add inp (word(c + 4)):int64`]) 2 3);;

let fml_d_byte,fml_d_tail,fml_d_loop = fml_copy_lemmas fml_d_copy;;

let FML_DE_CANONS_TAC =
  FML_CANONS_TAC
   ["X6",`word_add inp (word(ip + 4)):int64`;
    "X17",`word_add inp (word(c + 4)):int64`;
    "X7",`word_add inp (word(c + 4)):int64`];;

let SNAPPY_CF2_GCC12_O2_FML_D = prove
 (SNAPPY_CF2_GCC12_O2_FML_D_STMT,
  FML_MAIN_TAC fml_d_tail fml_d_loop 4 FML_DE_CANONS_TAC 2 3);;

let fml_e_byte,fml_e_tail,fml_e_loop = fml_copy_lemmas fml_e_copy;;

let SNAPPY_CF2_GCC12_O2_FML_E = prove
 (SNAPPY_CF2_GCC12_O2_FML_E_STMT,
  FML_MAIN_TAC fml_e_tail fml_e_loop 4 FML_DE_CANONS_TAC 2 3);;

(* ------------------------------------------------------------------------- *)
(* The copy C: +0x2d4 .. join10, s1 = c (X30), s2 = ip + 1 (X6), the index  *)
(* in X7.                                                                    *)
(* ------------------------------------------------------------------------- *)

let fml_c_post = fml_ml_post "CompressFragmentDoubleHash_join10" "X7" false;;

let fml_c_frame =
  "MAYCHANGE [PC; X6; X7; X17; X18; X19] ,,
   MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events]";;

(* loop15 (+0x71c).                                                          *)

let FML_C_BYTE = prove
 (fml_stmt
   ("read PC s = word(pc + 16892) /\\
    read X30 s = word_add inp (word a) /\\
    read X6 s = word_add inp (word(b + j)) /\\ " ^ fml_x16 ^ " /\\
    read X7 s = word j")
   fml_c_post fml_c_frame
   "a < b /\\ b + j < LENGTH src /\\
    snappy_match_length src a b = j + snappy_match_length src (a + j) (b + j)",
  FML_INDUCT_TAC `LENGTH(src:byte list) - (b + j)` THEN
  STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  FML_READ8_TAC `word_add (inp:int64) (word(b + j))` `b + j` THEN
  FML_READ8_TAC `word_add (word_add (inp:int64) (word a)) (word j)` `a + j` THEN
  ARM_BSTEP_TAC FML_EXEC (1--6) THEN
  FML_FACT_TAC FML_MATCH_LENGTH_STEP [`src:byte list`; `a + j`; `b + j`] THEN
  FML_BRANCH_TAC ~tac:FML_BYTE_EQ_TAC
    `EL (a + j) (src:byte list) = EL (b + j) src` THENL
   [ARM_BSTEP_TAC FML_EXEC (7--8) THEN
    FML_BRANCH_TAC `b + j + 1 < LENGTH(src:byte list)` THENL
     [ARM_BSTEP_TAC FML_EXEC (9--9) THEN
      FML_CANON_TAC "X6" `word_add inp (word(b + j + 1)):int64` THEN
      FML_CANON_TAC "X7" `word(j + 1):int64` THEN
      FML_IH_TAC [`j + 1`,"j"] "s10" THEN
      FML_FIN_TAC;
      ARM_BSTEP_TAC FML_EXEC (9--11) THEN
      FML_FACT_TAC FML_MATCH_LENGTH_END
        [`src:byte list`; `a + j + 1`; `b + j + 1`] THEN
      FML_FIN_TAC THEN FML_REG_TAC];
    FML_FIN_TAC THEN FML_REG_TAC]);;

(* join23 (+0x708): j bytes are known to match.                              *)

let FML_C_TAIL = prove
 (fml_stmt
   ("read PC s = word(pc + 16872) /\\
    read X30 s = word_add inp (word a) /\\
    read X6 s = word_add inp (word(b + j)) /\\ " ^ fml_x16 ^ " /\\
    read X7 s = word j /\\ read X19 s = word j")
   fml_c_post fml_c_frame
   "a < b /\\ b + j <= LENGTH src /\\
    snappy_match_length src a b = j + snappy_match_length src (a + j) (b + j)",
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ARM_BSTEP_TAC FML_EXEC (1--2) THEN
  FML_BRANCH_TAC `LENGTH(src:byte list) <= b + j` THENL
   [FML_FACT_TAC FML_MATCH_LENGTH_END [`src:byte list`; `a + j`; `b + j`] THEN
    FML_FIN_TAC THEN FML_REG_TAC;
    ARM_BSTEP_TAC FML_EXEC (3--4) THEN
    FML_CANON_TAC "X7" `word j:int64` THEN
    FML_CALL_TAC FML_C_BYTE [] "s5" THEN
    FML_FIN_TAC]);;

(* loop7 (+0x2f4).                                                           *)

let FML_C_LOOP = prove
 (fml_stmt
   ("read PC s = word(pc + 15828) /\\
    read X30 s = word_add inp (word a) /\\
    read X6 s = word_add inp (word(b + 8 * j)) /\\ " ^ fml_x16 ^ " /\\
    read X7 s = word(8 * j)")
   fml_c_post fml_c_frame
   "a < b /\\ b + 8 * j + 8 <= LENGTH src /\\
    snappy_match_length src a b =
    8 * j + snappy_match_length src (a + 8 * j) (b + 8 * j)",
  FML_INDUCT_TAC `LENGTH(src:byte list) - (b + 8 * j)` THEN
  STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  FML_READ64_TAC `word_add (word_add (inp:int64) (word a)) (word(8 * j))`
    `a + 8 * j` THEN
  FML_READ64_TAC `word_add (inp:int64) (word(b + 8 * j))` `b + 8 * j` THEN
  ARM_BSTEP_TAC FML_EXEC (1--5) THEN
  FML_BRANCH_TAC
   `snappy_load64 src (a + 8 * j) = snappy_load64 src (b + 8 * j)` THENL
   [FML_FACT_TAC SNAPPY_MATCH_LENGTH_EQ8
      [`src:byte list`; `a + 8 * j`; `b + 8 * j`] THEN
    ARM_BSTEP_TAC FML_EXEC (6--8) THEN
    FML_BRANCH_TAC `LENGTH(src:byte list) - 8 < b + 8 * j + 8` THENL
     [ARM_BSTEP_TAC FML_EXEC (9--10) THEN
      FML_CANON_TAC "X6" `word_add inp (word(b + 8 * j + 8)):int64` THEN
      FML_CANON_TAC "X7" `word(8 * j + 8):int64` THEN
      FML_CANON_TAC "X19" `word(8 * j + 8):int64` THEN
      FML_CALL_TAC FML_C_TAIL [`8 * j + 8`,"j"] "s11" THEN FML_FIN_TAC;
      ARM_BSTEP_TAC FML_EXEC (9--9) THEN
      FML_CANON_TAC "X6" `word_add inp (word(b + 8 * (j + 1))):int64` THEN
      FML_CANON_TAC "X7" `word(8 * (j + 1)):int64` THEN
      FML_IH_TAC [`j + 1`,"j"] "s10" THEN FML_FIN_TAC];
    FML_FACT_TAC SNAPPY_MATCH_LENGTH_NE8
      [`src:byte list`; `a + 8 * j`; `b + 8 * j`] THEN
    ARM_BSTEP_TAC FML_EXEC (6--8) THEN
    FML_KNOWN_BRANCH_TAC `LENGTH(src:byte list) - 8 < b + 8 * j` THEN
    ARM_BSTEP_TAC FML_EXEC (9--14) THEN
    FML_FIN_TAC THEN FML_CTZ_TAC]);;

let SNAPPY_CF2_GCC12_O2_FML_C = prove
 (SNAPPY_CF2_GCC12_O2_FML_C_STMT,
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ARM_BSTEP_TAC FML_EXEC (1--2) THEN
  FML_KNOWN_BRANCH_TAC `LENGTH(src:byte list) - 8 < ip + 1` THEN
  ARM_BSTEP_TAC FML_EXEC (3--4) THEN
  FML_CALL_TAC FML_C_LOOP [`c:num`,"a"; `ip + 1`,"b"; `0`,"j"] "s5" THEN
  FML_FIN_TAC);;
