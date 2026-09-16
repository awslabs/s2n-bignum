(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Functional correctness of polyz_unpack_19:                                *)
(* Unpack polynomial z with 20-bit packed coefficients (GAMMA1 = 2^19)       *)
(* Maps packed [0, 2^20-1] to signed [-(2^19-1), 2^19] via GAMMA1 - x        *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(**** print_literal_from_elf "arm/mldsa/mldsa_polyz_unpack_19.o";;
 ****)

let mldsa_polyz_unpack_19_mc = define_assert_from_elf
  "mldsa_polyz_unpack_19_mc" "arm/mldsa/mldsa_polyz_unpack_19.o"
[
  0x3dc00058;       (* arm_LDR Q24 X2 (Immediate_Offset (word 0)) *)
  0x3dc00459;       (* arm_LDR Q25 X2 (Immediate_Offset (word 16)) *)
  0x3dc0085a;       (* arm_LDR Q26 X2 (Immediate_Offset (word 32)) *)
  0x3dc00c5b;       (* arm_LDR Q27 X2 (Immediate_Offset (word 48)) *)
  0xd2c01f83;       (* arm_MOVZ X3 (word 252) 32 *)
  0x4e080c7c;       (* arm_DUP_GEN Q28 X3 64 128 *)
  0x4f00d5fd;       (* arm_MOVI Q29 (word 4503595333451775) *)
  0x4f00451e;       (* arm_MOVI Q30 (word 2251799814209536) *)
  0xd2800209;       (* arm_MOV X9 (rvalue (word 16)) *)
  0x4c40a020;       (* arm_LDP Q0 Q1 X1 No_Offset *)
  0x91006021;       (* arm_ADD X1 X1 (rvalue (word 24)) *)
  0x4cdf7022;       (* arm_LDR Q2 X1 (Postimmediate_Offset (word 16)) *)
  0x4e180004;       (* arm_TBL Q4 [Q0] Q24 128 *)
  0x4e192005;       (* arm_TBL2 Q5 Q0 Q1 Q25 128 *)
  0x4e1a0026;       (* arm_TBL Q6 [Q1] Q26 128 *)
  0x4e1b2027;       (* arm_TBL2 Q7 Q1 Q2 Q27 128 *)
  0x6ebc4484;       (* arm_USHL_VEC Q4 Q4 Q28 32 128 *)
  0x4e3d1c84;       (* arm_AND_VEC Q4 Q4 Q29 128 *)
  0x6ea487c4;       (* arm_SUB_VEC Q4 Q30 Q4 32 128 *)
  0x6ebc44a5;       (* arm_USHL_VEC Q5 Q5 Q28 32 128 *)
  0x4e3d1ca5;       (* arm_AND_VEC Q5 Q5 Q29 128 *)
  0x6ea587c5;       (* arm_SUB_VEC Q5 Q30 Q5 32 128 *)
  0x6ebc44c6;       (* arm_USHL_VEC Q6 Q6 Q28 32 128 *)
  0x4e3d1cc6;       (* arm_AND_VEC Q6 Q6 Q29 128 *)
  0x6ea687c6;       (* arm_SUB_VEC Q6 Q30 Q6 32 128 *)
  0x6ebc44e7;       (* arm_USHL_VEC Q7 Q7 Q28 32 128 *)
  0x4e3d1ce7;       (* arm_AND_VEC Q7 Q7 Q29 128 *)
  0x6ea787c7;       (* arm_SUB_VEC Q7 Q30 Q7 32 128 *)
  0x3d800405;       (* arm_STR Q5 X0 (Immediate_Offset (word 16)) *)
  0x3d800806;       (* arm_STR Q6 X0 (Immediate_Offset (word 32)) *)
  0x3d800c07;       (* arm_STR Q7 X0 (Immediate_Offset (word 48)) *)
  0x3c840404;       (* arm_STR Q4 X0 (Postimmediate_Offset (word 64)) *)
  0xf1000529;       (* arm_SUBS X9 X9 (rvalue (word 1)) *)
  0x54fffd01;       (* arm_BNE (word 2097056) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let MLDSA_POLYZ_UNPACK_19_EXEC = ARM_MK_EXEC_RULE mldsa_polyz_unpack_19_mc;;

(* ------------------------------------------------------------------------- *)
(* Code length constants                                                     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_MLDSA_POLYZ_UNPACK_19_MC =
  REWRITE_CONV[mldsa_polyz_unpack_19_mc] `LENGTH mldsa_polyz_unpack_19_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let MLDSA_POLYZ_UNPACK_19_PREAMBLE_LENGTH = new_definition
  `MLDSA_POLYZ_UNPACK_19_PREAMBLE_LENGTH = 0`;;

let MLDSA_POLYZ_UNPACK_19_POSTAMBLE_LENGTH = new_definition
  `MLDSA_POLYZ_UNPACK_19_POSTAMBLE_LENGTH = 4`;;

let MLDSA_POLYZ_UNPACK_19_CORE_START = new_definition
  `MLDSA_POLYZ_UNPACK_19_CORE_START = MLDSA_POLYZ_UNPACK_19_PREAMBLE_LENGTH`;;

let MLDSA_POLYZ_UNPACK_19_CORE_END = new_definition
  `MLDSA_POLYZ_UNPACK_19_CORE_END =
     LENGTH mldsa_polyz_unpack_19_mc - MLDSA_POLYZ_UNPACK_19_POSTAMBLE_LENGTH`;;

let LENGTH_SIMPLIFY_CONV_19 =
  REWRITE_CONV[LENGTH_MLDSA_POLYZ_UNPACK_19_MC;
              MLDSA_POLYZ_UNPACK_19_CORE_START; MLDSA_POLYZ_UNPACK_19_CORE_END;
              MLDSA_POLYZ_UNPACK_19_PREAMBLE_LENGTH;
              MLDSA_POLYZ_UNPACK_19_POSTAMBLE_LENGTH] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV [ADD_0];;

(* ------------------------------------------------------------------------- *)
(* ARM-specific SIMD lane machinery (128-bit NEON layout): base-word         *)
(* simplifications, the zunpack TBL/USHL lane conversions, and the unaligned *)
(* overlapping-read splitter/deriver. Inlined as they are aarch64-specific.  *)
(* ------------------------------------------------------------------------- *)

let mk_base_simps d =
  let total = 16 * d in
  let rem = total - 256 in
  let total_ty = mk_finty (Num.num_of_int total) in
  let rem_ty = mk_finty (Num.num_of_int rem) in
  let mod_128 = CONV_RULE NUM_REDUCE_CONV (prove(
    inst [total_ty, `:N`]
      `word (t MOD 2 EXP 128) : 128 word =
       word_subword (word t : N word) (0, 128)`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_128] THEN
    REWRITE_TAC[EXP; DIV_1; MOD_MOD_REFL; MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    MP_TAC (SPECL [`t:num`; `2`; mk_small_numeral total; `128`] MOD_MOD_EXP_MIN) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REFL_TAC)) in
  let div_128_mod_128 = CONV_RULE NUM_REDUCE_CONV (prove(
    inst [total_ty, `:N`]
      `word ((t DIV 2 EXP 128) MOD 2 EXP 128) : 128 word =
       word_subword (word t : N word) (128, 128)`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_128] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    REWRITE_TAC[ARITH_RULE `MIN 128 128 = 128`; MOD_MOD_REFL] THEN
    REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
    CONV_TAC NUM_REDUCE_CONV)) in
  let div_256 = CONV_RULE NUM_REDUCE_CONV (prove(
    inst [total_ty, `:N`; rem_ty, `:M`]
      `word (t DIV 2 EXP 256) : M word =
       word_subword (word t : N word) (256, dimindex(:M))`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL])) in
  [mod_128; div_128_mod_128; div_256];;

let ZUNPACK_LANE_CONV d i tm =
  let gamma1 = 1 lsl (d - 1) in
  let word_bits = 16 * d in
  let t_ty = mk_finty (Num.num_of_int word_bits) in
  let is_target t =
    try fst(dest_type(type_of t)) = "word" &&
        Num.int_of_num(dest_finty(hd(snd(dest_type(type_of t))))) = word_bits
    with _ -> false in
  let t_var_opt = try Some(find_term is_target tm) with _ -> None in
  match t_var_opt with
  | Some t_var ->
      let d_ty = mk_finty (Num.num_of_int d) in
      let goal = mk_eq(tm,
        subst [mk_small_numeral (d*i), `pos:num`;
               mk_small_numeral d, `bw:num`;
               mk_small_numeral gamma1, `g:num`;
               t_var, mk_var("t", mk_type("word",[t_ty]))]
          (inst [d_ty, `:B`; t_ty, `:T`]
            `word_sub (word g : 32 word)
                      (word_zx (word_subword (t : T word) (pos,bw) : B word))`)) in
      WORD_BLAST goal
  | None -> failwith ("ZUNPACK_LANE_CONV: no " ^ string_of_int word_bits ^ "-bit word");;

let ZUNPACK_128_CONV d tm =
  tryfind (fun base_i ->
    let f i = ZUNPACK_LANE_CONV d (base_i + i) in
    RAND_CONV (
      COMB2_CONV
        (RAND_CONV (COMB2_CONV (RAND_CONV (f 3)) (f 2)))
        (COMB2_CONV (RAND_CONV (f 1)) (f 0)))
    tm) [0; 4; 8; 12];;

let SIMP_ZUNPACK_TAC d zunpack_correct =
  let zunpack_const =
    fst(strip_comb(rhs(snd(strip_forall(concl zunpack_correct))))) in
  let already_processed tm =
    can (find_term ((=) zunpack_const)) tm in
  RULE_ASSUM_TAC (fun th ->
    if already_processed (concl th) then th
    else CONV_RULE (TRY_CONV (ZUNPACK_128_CONV d) THENC
                    TRY_CONV (ONCE_REWRITE_CONV [zunpack_correct])) th);;

let split_k_l_at base k l =
  let a_tm = mk_comb(mk_comb(`word_add:int64->int64->int64`, `a:int64`),
    mk_comb(`word:num->int64`, mk_small_numeral base)) in
  CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV THENC DEPTH_CONV NUM_MULT_CONV)
    (INST [mk_small_numeral k,`k:num`; mk_small_numeral l,`l:num`;
           a_tm, `a:int64`] READ_BYTES_SPLIT_ANY);;


let BYTES128_FROM_OVERLAP_64 = prove
 (`read (memory :> bytes128 (word_add a (word 16))) (s:armstate) = (word m16 : int128) /\
   read (memory :> bytes64 (word_add a (word 32))) (s:armstate) = (word m64 : int64)
   ==> read (memory :> bytes128 (word_add a (word 24))) s =
       (word_join (word m64 : int64) (word(m16 DIV 2 EXP 64) : int64) : int128)`,
  REWRITE_TAC[BYTES128_WBYTES; BYTES64_WBYTES; READ_COMPONENT_COMPOSE;
              GSYM VAL_EQ; VAL_READ_WBYTES] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ABBREV_TAC `m = read memory (s:armstate)` THEN
  REWRITE_TAC[VAL_WORD_JOIN; DIMINDEX_64; VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ONCE_REWRITE_TAC[split_k_l_at 16 8 8] THEN
  ONCE_REWRITE_TAC[split_k_l_at 24 8 8] THEN
  REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  let COMMON_SETUP =
    SUBGOAL_THEN
     `(m16 DIV 18446744073709551616) MOD 18446744073709551616 < 18446744073709551616 /\
      m64 MOD 18446744073709551616 < 18446744073709551616`
     STRIP_ASSUME_TAC
      THENL [REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(18446744073709551616 * m64 MOD 18446744073709551616 +
       (m16 DIV 18446744073709551616) MOD 18446744073709551616) <
      340282366920938463463374607431768211456`
     ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_LT] in
  CONJ_TAC THENL [
    COMMON_SETUP THEN
    REWRITE_TAC[MOD_MULT_ADD; MOD_MOD_EXP_MIN; GSYM EXP_ADD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
    REWRITE_TAC[GSYM(CONV_RULE NUM_REDUCE_CONV
      (SPECL [`m16:num`; `18446744073709551616`; `18446744073709551616`] DIV_MOD))];
    COMMON_SETUP THEN
    SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN ASM_SIMP_TAC[DIV_LT] THEN ARITH_TAC]);;

(* Instantiate overlap theorem for chunk i and ASSUME_TAC the result *)
let DERIVE_OVERLAP_TAC overlap_thm chunk_size i =
  let off16 = chunk_size*i + 16 and off32 = chunk_size*i + 32 in
  let w16 = mk_small_numeral off16 and w32 = mk_small_numeral off32 in
  let has t th = can (find_term ((=) t)) (concl th) in
  let a_val = mk_comb(mk_comb(`word_add:int64->int64->int64`, `b:int64`),
    mk_comb(`word:num->int64`, mk_small_numeral (chunk_size * i))) in
  let inst = INST [a_val, `a:int64`; `s0:armstate`, `s:armstate`] overlap_thm in
  let thm = CONV_RULE (ONCE_DEPTH_CONV(GEN_REWRITE_CONV I [WORD_ADD_ASSOC_CONSTS]) THENC
             DEPTH_CONV NUM_ADD_CONV) inst in
  FIRST_ASSUM(fun th128 ->
    if not(has w16 th128 && has `bytes128` th128 && has `b:int64` th128) then failwith "" else
    FIRST_ASSUM(fun thtail ->
      if not(has w32 thtail && has `b:int64` thtail &&
             not(has `bytes128` thtail)) then failwith "" else
      ASSUME_TAC(MATCH_MP thm (CONJ th128 thtail))));;


(* ------------------------------------------------------------------------- *)
(* D=20 instantiations for SIMD infrastructure                               *)
(* ------------------------------------------------------------------------- *)

let BASE_SIMPS_D20 = mk_base_simps 20;;
let NUM_OF_WORDLIST_SPLIT_20_256 = mk_split_theorem 20 256 16;;
let READ_MEMORY_WBYTES_SPLIT_128_128_64 = prove
 (`t < 2 EXP 320
    ==> (read (memory :> wbytes a) (s:armstate) = (word t : 320 word) <=>
         read (memory :> bytes128 a) s = (word (t MOD 2 EXP 128) : int128) /\
         read (memory :> bytes128 (word_add a (word 16))) s =
         (word ((t DIV 2 EXP 128) MOD 2 EXP 128) : int128) /\
         read (memory :> bytes64 (word_add a (word 32))) s =
         (word (t DIV 2 EXP 256) : int64))`,
  let split_16_24 = CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV THENC
                                DEPTH_CONV NUM_MULT_CONV)
    (INST [`16`,`k:num`; `24`,`l:num`] READ_BYTES_SPLIT_ANY) in
  let split_16_8 = CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV THENC
                               DEPTH_CONV NUM_MULT_CONV)
    (INST [`16`,`k:num`; `8`,`l:num`] READ_BYTES_SPLIT_ANY) in
  STRIP_TAC THEN
  REWRITE_TAC[BYTES128_WBYTES; BYTES64_WBYTES; GSYM VAL_EQ;
              VAL_READ_WBYTES; READ_COMPONENT_COMPOSE] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[split_16_24] THEN REWRITE_TAC[split_16_8] THEN
  REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  IMP_REWRITE_TAC[VAL_WORD_EXACT] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ASM_ARITH_TAC);;
let WORD_SUBWORD_NUM_OF_WORDLIST_CASES_D20 = mk_subword_cases 20 16;;

(* ------------------------------------------------------------------------- *)
(* Core correctness theorem                                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_POLYZ_UNPACK_19_CORRECT = prove
 (`!r b t (l:(20 word) list) pc.
        LENGTH l = 256 /\
        ALLPAIRS nonoverlapping
         [(r,1024)]
         [(word pc,LENGTH mldsa_polyz_unpack_19_mc); (b,640); (t,64)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mldsa_polyz_unpack_19_mc /\
                  read PC s = word (pc + MLDSA_POLYZ_UNPACK_19_CORE_START) /\
                  C_ARGUMENTS [r; b; t] s /\
                  read(memory :> bytes(t,64)) s =
                    num_of_wordlist mldsa_polyz_unpack_19_indices /\
                  read(memory :> bytes(b,640)) s = num_of_wordlist l)
             (\s. read PC s = word(pc + MLDSA_POLYZ_UNPACK_19_CORE_END) /\
                  read(memory :> bytes(r,1024)) s =
                       num_of_wordlist (MAP zunpack19 l))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV_19 THEN
  MAP_EVERY X_GEN_TAC [`r:int64`; `b:int64`; `t:int64`;
                        `l:(20 word) list`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              NONOVERLAPPING_CLAUSES; ALL; ALLPAIRS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  ENSURES_INIT_TAC "s0" THEN

  (*** Expand table precondition into 4 x bytes128 reads ***)
  FIRST_X_ASSUM(MP_TAC o check (can (term_match []
    `read(memory :> bytes(t:int64,64)) s = x`) o concl)) THEN
  REWRITE_TAC[mldsa_polyz_unpack_19_indices] THEN
  REPLICATE_TAC 4
   (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
         [GSYM NUM_OF_PAIR_WORDLIST]) THEN
  REWRITE_TAC[pair_wordlist] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  REWRITE_TAC[GSYM BYTES128_WBYTES] THEN
  STRIP_TAC THEN

  (*** Split 256 20-bit coefficients into 16 chunks of 16 as 320-bit words ***)
  UNDISCH_TAC `read(memory :> bytes(b,640)) s0 = num_of_wordlist(l:(20 word) list)` THEN
  IMP_REWRITE_TAC [NUM_OF_WORDLIST_SPLIT_20_256] THEN
  CONV_TAC (ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC [MAP; o_DEF] THEN
  CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN

  (*** Split each 320-bit wbytes into bytes128 + bytes128 + bytes64 ***)
  IMP_REWRITE_TAC [READ_MEMORY_WBYTES_SPLIT_128_128_64] THEN
  MAP_EVERY (fun n -> SUBGOAL_THEN (subst[mk_small_numeral n,`k:num`]
    `num_of_wordlist (SUB_LIST (16 * k,16) (l : (20 word) list)) < 2 EXP 320`)
     (fun th -> REWRITE_TAC[th]) THENL [
       TRANS_TAC LTE_TRANS (subst[mk_small_numeral n,`k:num`]
                            `2 EXP (dimindex(:20) * LENGTH(SUB_LIST(16*k,16) (l : (20 word) list)))`) THEN
       REWRITE_TAC[NUM_OF_WORDLIST_BOUND] THEN
       REWRITE_TAC[LENGTH_SUB_LIST; DIMINDEX_CONV `dimindex (:20)`] THEN
       ASM_SIMP_TAC [] THEN NUM_REDUCE_TAC;
       ALL_TAC]) (0--15) THEN
  REWRITE_TAC [WORD_ADD_ASSOC_CONSTS] THEN CONV_TAC (TOP_SWEEP_CONV NUM_ADD_CONV) THEN
  STRIP_TAC THEN

  (*** Derive overlapping bytes128 reads at offset 24 for each chunk ***)
  MAP_EVERY (DERIVE_OVERLAP_TAC BYTES128_FROM_OVERLAP_64 40) (0--15) THEN

  (*** Gather LENGTH assumptions for sublists ***)
  MAP_EVERY (fun i -> SUBGOAL_THEN
    (subst [mk_small_numeral (16 * i), `i: num`]
      `LENGTH (SUB_LIST (i, 16) (l : (20 word) list)) = 16`) ASSUME_TAC
    THENL [ASM_REWRITE_TAC [LENGTH_SUB_LIST] THEN NUM_REDUCE_TAC; ALL_TAC])
    (0 -- 15) THEN

  (*** Symbolic execution with per-step simplification ***)
  MAP_UNTIL_TARGET_PC (fun n ->
    ARM_STEPS_TAC MLDSA_POLYZ_UNPACK_19_EXEC [n] THEN
    SIMD_SIMPLIFY_TAC (map GSYM BASE_SIMPS_D20) THEN
    SIMP_ZUNPACK_TAC 20 ZUNPACK19_CORRECT) 1 THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Fold output back to MAP zunpack19 l ***)
  REPEAT (FIRST_X_ASSUM(MP_TAC o check
     (can (term_match [] `read (memory :> bytes128 r) s0 = xxx`) o concl))) THEN
  TRY (IMP_REWRITE_TAC WORD_SUBWORD_NUM_OF_WORDLIST_CASES_D20) THEN
  UNDISCH_THEN `LENGTH (l : (20 word) list) = 256`
    (fun th -> CONV_TAC (TOP_SWEEP_CONV (EL_SUB_LIST_CONV th)) THEN ASSUME_TAC th) THEN
  REPEAT DISCH_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV) [GSYM LIST_OF_SEQ_EQ_SELF] THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN
  CONV_TAC (TOP_SWEEP_CONV LIST_OF_SEQ_CONV) THEN
  ASM_REWRITE_TAC [MAP] THEN
  REPLICATE_TAC 2 (CONV_TAC (ONCE_REWRITE_CONV [GSYM NUM_OF_PAIR_WORDLIST])) THEN
  REWRITE_TAC[pair_wordlist] THEN
  CONV_TAC (ONCE_DEPTH_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[GSYM BYTES128_WBYTES]);;

(* ------------------------------------------------------------------------- *)
(* Subroutine correctness                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_POLYZ_UNPACK_19_SUBROUTINE_CORRECT = prove
 (`!r b t (l:(20 word) list) pc returnaddress.
        LENGTH l = 256 /\
        ALLPAIRS nonoverlapping
         [(r,1024)]
         [(word pc,LENGTH mldsa_polyz_unpack_19_mc); (b,640); (t,64)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mldsa_polyz_unpack_19_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; b; t] s /\
                  read(memory :> bytes(t,64)) s =
                    num_of_wordlist mldsa_polyz_unpack_19_indices /\
                  read(memory :> bytes(b,640)) s = num_of_wordlist l)
             (\s. read PC s = returnaddress /\
                  read(memory :> bytes(r,1024)) s =
                       num_of_wordlist (MAP zunpack19 l) /\
                  (!i. i < 256 ==>
                       --(&(2 EXP 19) - &1) <= ival(EL i (MAP zunpack19 l)) /\
                       ival(EL i (MAP zunpack19 l)) <= &(2 EXP 19)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV_19 THEN
  ARM_ADD_RETURN_NOSTACK_TAC MLDSA_POLYZ_UNPACK_19_EXEC
   (CONV_RULE LENGTH_SIMPLIFY_CONV_19 MLDSA_POLYZ_UNPACK_19_CORRECT) THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV
    (ISPECL [`l:(20 word) list`; `i:num`] ZUNPACK19_MAP_BOUND)) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mldsa_polyz_unpack_19_arm" subroutine_signatures)
    MLDSA_POLYZ_UNPACK_19_SUBROUTINE_CORRECT
    MLDSA_POLYZ_UNPACK_19_EXEC;;

let MLDSA_POLYZ_UNPACK_19_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r b t (l:(20 word) list) pc returnaddress.
           LENGTH l = 256 /\
           ALLPAIRS nonoverlapping
            [(r,1024)]
            [(word pc,LENGTH mldsa_polyz_unpack_19_mc); (b,640); (t,64)]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mldsa_polyz_unpack_19_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; b; t] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events b t r pc returnaddress /\
                         memaccess_inbounds e2 [b,640; t,64; r,1024]
                         [r,1024]))
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLDSA_POLYZ_UNPACK_19_EXEC);;
