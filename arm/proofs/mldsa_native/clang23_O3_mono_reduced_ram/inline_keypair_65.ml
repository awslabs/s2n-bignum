(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The inlined code of mldsa65_keypair_internal in the clang 23 -O3          *)
(* monolithic reduced-RAM build, as lemmas for the proof of its statement.   *)
(* The frame is at fp (the stack pointer after the prologue, 5792 bytes):    *)
(* the five polynomial buffers at fp + 192 + 1024 k, the input of the seed   *)
(* SHAKE256 at fp + 5376, the seed buffer (rho, rho', key) at fp + 5440, the *)
(* state of the SHAKE256 of the public key at fp + 5568, tr at fp + 5312 and *)
(* the canary at fp + 5784.                                                  *)
(*                                                                           *)
(* - KI65_SEED: the SHAKE256 of the seed extended by k = 6 and l = 5. The    *)
(*   code is that of mldsa44 (KI_SEED_PROVE of inline_keypair.ml) with other *)
(*   offsets and registers, and its state is in the first polynomial buffer  *)
(*   (fp + 192) rather than above the seed buffer, so it has its own         *)
(*   statement (KI65_SEED_TERM); the proof uses the tactics of KI_SEED_PROVE *)
(*   with two records: KS65 for the input and the seed buffer, KS65S for the *)
(*   state (its ks_d places the state at 4384 + ks_d = 192).                 *)
(* - KP65_PACK: the packing of s1 and s2 into the secret key (eta = 4, four  *)
(*   bits per coefficient, mld_polyeta_pack_4), see KP_PACK4_TERM below.     *)
(* - KI65_SHAKE: the SHAKE256 of the public key (KI_SHAKE65_INST of          *)
(*   inline_keypair.ml).                                                     *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_keypair.ml";;

(* ------------------------------------------------------------------------- *)
(* The SHAKE256 of the seed: from the ADRP after the probe of the stack to   *)
(* the first call of poly_uniform_eta_4x (nonces 7 to 10, the polynomials at *)
(* fp + 192 + 1024 k, rho' at fp + 5472).                                    *)
(* ------------------------------------------------------------------------- *)

let KS65 = { ks_fn = "mldsa65_keypair_internal"; ks_st = 0x10db4; ks_en = 0x10f78;
             ks_d = 1184; ks_poly = 192; ks_k = 6; ks_l = 5; ks_n0 = 7 };;

let KS65S = { KS65 with ks_d = 192 - 4384 };;

let KI65_SEED_TERM =
  let p = KS65 in
  parse_term(INLINE_FILL
 "exists f_events.
    forall e (fp:int64) (pk:int64) (sk:int64) (seed:int64) SEED guard canary pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 16 fp /\\ aligned 32 fp /\\
      nonoverlapping (word_sub fp (word 240),6032) (word pc,libmldsa_size) /\\
      nonoverlapping (word_sub fp (word 240),6032) (seed,32) /\\
      nonoverlapping (word_sub fp (word 240),6032)
                     (word_add (word pc) (word got_stack_chk_guard),8) /\\
      nonoverlapping (word_sub fp (word 240),6032) (guard,8)
      ==> ensures arm
           (\\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read PC s = word (pc + @ST@) /\\
                read SP s = fp /\\ read X0 s = pk /\\ read X1 s = sk /\\
                read X2 s = seed /\\
                read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard))) s =
                  guard /\\
                read (memory :> bytes64 guard) s = canary /\\
                read (memory :> bytes(seed,32)) s = SEED /\\
                read events s = e)
           (\\s. read PC s = word (pc + @EN@) /\\
                read SP s = fp /\\
                read X0 s = word_add fp (word 192) /\\
                read X1 s = word_add fp (word 1216) /\\
                read X2 s = word_add fp (word 2240) /\\
                read X3 s = word_add fp (word 3264) /\\
                read X4 s = word_add fp (word 5472) /\\
                read X5 s = word 7 /\\ read X6 s = word 8 /\\ read X7 s = word 9 /\\
                read X19 s = sk /\\ read X20 s = pk /\\
                read X21 s = word_add fp (word 3264) /\\
                read X22 s = word_add fp (word 192) /\\
                read X25 s = word_add fp (word 1216) /\\
                read X28 s = word_add fp (word 2240) /\\
                read (memory :> bytes8 fp) s = word 10 /\\
                read (memory :> bytes64 (word_add fp (word 5784))) s = canary /\\
                read (memory :> bytes(word_add fp (word 5440),128)) s =
                  num_of_bytelist
                   (list_of_seq
                     (mld_shake256_byte 34 (SEED + 2 EXP 256 * (6 + 256 * 5))) 128) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events seed guard pc fp /\\
                   memaccess_inbounds e2
                    [seed,32; word_sub fp (word 240),240; fp,5792;
                     word_add (word pc) (word got_stack_chk_guard),8; guard,8;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192]
                    [word_sub fp (word 240),240; fp,5792]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [X18; X19; X20; X21; X22; X25; X28; X30] ,,
            MAYCHANGE [memory :> bytes(word_sub fp (word 240),240);
                       memory :> bytes(fp,5792)])"
  ["ST",string_of_int p.ks_st; "EN",string_of_int p.ks_en]);;

(*** The steps as in KI_SEED_PROVE: the ORR at step 16, the stores that   ***)
(*** later loads read in parts at steps 22 (state + 24), 23 (input + 16), ***)
(*** 42 (input + 32, k and l) and 46 (state + 120), the state complete    ***)
(*** after step 77 and the call of the permutation at step 78             ***)

let KI65_SEED_PROVE () =
  let p = KS65 and ps = KS65S in
  let exec = ARM_MK_EXEC_RANGES_RULE
    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
    [(p.ks_st,p.ks_en); layout_range "mldsa_keccakf1600_permute"] in
  let sw = KS_SW_OF (KS_KL p) in
  prove(KI65_SEED_TERM,
   ASSUME_CALLEE_SAFETY_TAILED_TAC
     MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600
     "H_PERM" THEN
   CONCRETIZE_F_EVENTS_TAC
    `\(seed:int64) (guard:int64) (pc:num) (fp:int64).
       f_ev_sd seed guard pc fp :(uarch_event)list` THEN
   META_EXISTS_TAC THEN
   REWRITE_TAC[NONOVERLAPPING_CLAUSES; fst exec] THEN
   REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
   FULL_INIT_TAC THEN KS_SEED_BYTES_TAC THEN KS_SEED128_TAC THEN
   ARM_STEPS_TAC exec [1] THEN MLKEM_NATIVE_ADRP_TAC THEN
   ARM_STEPS_TAC exec (2--16) THEN KS_ORR_TAC p THEN
   ARM_STEPS_TAC exec (17--22) THEN KS_SPLIT_TAC "s22" 216 128 THEN
   ARM_STEPS_TAC exec [23] THEN KS_SPLIT_TAC "s23" 5392 128 THEN
   ARM_STEPS_TAC exec (24--42) THEN KS_SPLIT_TAC "s42" 5408 16 THEN
   ARM_STEPS_TAC exec (43--46) THEN KS_SPLIT_TAC "s46" 312 128 THEN
   ARM_STEPS_TAC exec (47--77) THEN
   KS_CHAIN_TAC ps "s77" THEN
   FIRST_ASSUM(fun th ->
     if can (term_match []
          `read (memory :> bytes(word_add fp (word 192),200)) s77 = x`) (concl th)
     then ASSUME_TAC(REWRITE_RULE[GSYM READ_MEMORY_WBYTES_1600]
            (CONV_RULE(RAND_CONV(REWRITE_CONV[ARITH_RULE `8 * 200 = 1600`;
                                              KS_MODLEMMA])) th))
     else NO_TAC) THEN
   ARM_STEPS_TAC exec [78] THEN
   FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc exec "H_PERM"
    [`read X0 s`; sw; `pc:num`; `read SP s`; `read X30 s`]
    [`seed:int64`; `guard:int64`; `pc:num`; `fp:int64`] 79 THEN
   KS_STATE_CHUNKS_TAC ps "s79" THEN
   ARM_STEPS_TAC exec (80--114) THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL [KS_OUT_TAC p "s114"; DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The packing of s1 and s2 (eta = 4). After each call of                    *)
(* poly_uniform_eta_4x the code packs the polynomials it sampled (four, or   *)
(* three after the second call, whose last output is not used) without loops *)
(* and without branches: LD2 of 32 bytes (8 coefficients) splits the even    *)
(* and the odd coefficients, UZP1 .8h and .16b narrow them to bytes, SUB     *)
(* computes 4 - c bytewise (and 0x40 - (c << 4) after SHL by 4 for the odd   *)
(* ones), ORR joins the two nibbles, and STR or STP stores 16 bytes of the   *)
(* secret key at sk + off (sk in X19). Clang spills vectors to the stack at  *)
(* fp + 16 .. fp + 176, zeroes a slot at fp + 5568 for each polynomial (the  *)
(* mld_zeroize of the C function) and interleaves the setup of the next call *)
(* (the arguments in X0 to X7 and the fourth nonce at fp) with the packing.  *)
(* This is the code of polyw1_pack_32 as clang inlines it into               *)
(* mldsa65_verify_internal (inline_sign_w1pack32.ml), whose tactics the      *)
(* proof uses.                                                               *)
(*                                                                           *)
(* A region [st, en) is stated with the polynomials c0, c1, ... at fp + in   *)
(* and their packings at sk + out for the pairs (in, out) of polys, which    *)
(* the code writes to the contiguous range of the secret key from the least  *)
(* out; with                                                                 *)
(*   pre     extra facts about the state before, each followed by /\         *)
(*   post    extra facts about the state after, each followed by /\          *)
(*   regs    the X registers that change, after PC                           *)
(*   stores  the ranges (offset, size) from fp that the region writes        *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_w1pack32.ml";;

type kpack4 =
  { k4_st : int; k4_en : int; k4_polys : (int * int) list;
    k4_pre : string; k4_post : string; k4_regs : string;
    k4_stores : (int * int) list };;

let KP4_FN = "mldsa65_keypair_internal";;

let KP4_VAR k = mk_var("c"^string_of_int k,`:num->int32`);;

let KP4_OUT p =
  let outs = map snd p.k4_polys in
  (end_itlist min outs, 128 * length outs);;

let KP_PACK4_TERM p =
  let ss = Printf.sprintf in
  let ol,on = KP4_OUT p in
  let n = length p.k4_polys in
  let rng (a,m) = if a = 0 then ss "fp,%d" m else ss "word_add fp (word %d),%d" a m in
  let outr = ss "word_add sk (word %d),%d" ol on in
  let vars = String.concat " " (map (fun k -> ss "(c%d:num->int32)" k) (0--(n-1))) in
  let nov = String.concat "" (map (fun r ->
      ss "      nonoverlapping (%s) (word pc,libmldsa_size) /\\\n" (rng r)) p.k4_stores) in
  let ins = String.concat "" (map (fun (k,(i,_)) ->
      ss "                (!i. i < 256\n                     ==> read (memory :> bytes32 (word_add fp (word (%d + 4 * i)))) s =\n                         c%d i) /\\\n" i k)
      (zip (0--(n-1)) p.k4_polys)) in
  let outs = String.concat "" (map (fun (k,(_,u)) ->
      ss "                (!j. j < 128\n                     ==> read (memory :> bytes8 (word_add sk (word (%d + j)))) s =\n                         mld_polyeta_pack_4 c%d j) /\\\n" u k)
      (zip (0--(n-1)) p.k4_polys)) in
  let racc = String.concat "; " (map (fun (i,_) -> rng (i,1024)) p.k4_polys @
                                 map rng p.k4_stores) in
  let wacc = String.concat "" (map (fun r -> "; " ^ rng r) p.k4_stores) in
  let smem = String.concat "" (map (fun r -> ";\n                       memory :> bytes(" ^ rng r ^ ")") p.k4_stores) in
  parse_term(ss
 "exists f_events.
    forall e (sk:int64) (fp:int64) %s pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 16 fp /\\
      nonoverlapping (%s) (word pc,libmldsa_size) /\\
      nonoverlapping (%s) (fp,5792) /\\
%s      T
      ==> ensures arm
           (\\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read PC s = word (pc + %d) /\\
                read SP s = fp /\\ read X19 s = sk /\\ %s
%s                read events s = e)
           (\\s. read PC s = word (pc + %d) /\\ %s
%s                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events sk fp pc /\\
                   memaccess_inbounds e2 [%s] [%s%s]))
           (MAYCHANGE [PC; %s] ,,
            MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12;
                       Q13; Q14; Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23;
                       Q24; Q25; Q26; Q27; Q28; Q29; Q30; Q31] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(%s)%s])"
  vars outr outr nov
  p.k4_st p.k4_pre ins
  p.k4_en p.k4_post outs racc outr wacc
  p.k4_regs outr smem);;

(*** Byte j of polynomial k of the output: the 128-bit store that holds ***)
(*** it, the byte extracted (W1P_EXTRACT_CONV), and the packing by      ***)
(*** bit-blasting on the two coefficients it depends on                 ***)

let KP4_BYTE_TAC stores =
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_ADD_CONV)) THEN
  W(fun (asl,w) ->
    let gaddr = rand(rand(rand(rator(lhs w)))) in
    let off = dest_small_numeral(rand(rand gaddr)) in
    let base = lhand gaddr in
    let t = off mod 16 in
    let a16 = mk_comb(mk_comb(`word_add:int64->int64->int64`,base),
                      mk_comb(`word:num->int64`,mk_small_numeral(off - t))) in
    let sth = find (fun th -> rand(rand(rand(rator(lhs(concl th))))) = a16) stores in
    let bth = MP (SPECL [a16; rhs(concl sth); rand(lhs(concl sth));
                         mk_small_numeral t] INLINE_BYTES8_OF_BYTES128)
                 (CONJ sth (EQT_ELIM(NUM_REDUCE_CONV
                    (mk_binop `(<):num->num->bool` (mk_small_numeral t) `16`)))) in
    let bth = CONV_RULE(RAND_CONV(RAND_CONV(LAND_CONV NUM_MULT_CONV) THENC
                                  W1P_EXTRACT_CONV) THENC
                        ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) bth in
    GEN_REWRITE_TAC LAND_CONV [bth]) THEN
  REWRITE_TAC[mld_polyeta_pack_4] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV THENC DEPTH_CONV NUM_RED_CONV) THEN
  REWRITE_TAC[] THEN
  CPT_BLAST2_TAC (map KP4_VAR (0--3));;

let KP4_BYTES_TAC =
  CONV_TAC EXPAND_CASES_CONV THEN
  W(fun (asl,w) ->
    let stores = mapfilter (fun (_,th) ->
      let c = concl th in
      if is_eq c &&
         (try fst(dest_const(rator(rand(rand(rator(lhs c)))))) = "bytes128" &&
              lhand(rand(rand(rand(rator(lhs c))))) = `sk:int64`
          with Failure _ -> false)
      then th else fail()) asl in
    REPEAT CONJ_TAC THEN KP4_BYTE_TAC stores);;

(*** The 256-bit words read by LD2 as joins of 8 coefficients, without the ***)
(*** 128-bit facts that INLINE_MAP_INPUT_TAC adds                          ***)

let KP4_INPUT_TAC p =
  MAP_EVERY (fun (k,(i,_)) ->
    INLINE_MAP_INPUT_TAC i (KP4_VAR k) THEN INLINE_MAP_INPUT256_TAC i)
   (zip (0--(length p.k4_polys - 1)) p.k4_polys) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes128 a) (s0:armstate) = x`) (concl th)
    then ALL_TAC else NO_TAC));;

let KP4_IS_BYTES tm =
  try let _,b = dest_forall tm in
      can (find_term (fun t -> try fst(dest_const t) = "mld_polyeta_pack_4"
                               with Failure _ -> false)) b
  with Failure _ -> false;;

let KP_PACK4_PROVE p =
  let exec = INLINE_LOOP_EXEC (string_of_int p.k4_st) (string_of_int p.k4_en) in
  let nsteps = (p.k4_en - p.k4_st) / 4 in
  prove(KP_PACK4_TERM p,
   CONCRETIZE_F_EVENTS_TAC
    `\(sk:int64) (fp:int64) (pc:num). f_ev_kp sk fp pc :(uarch_event)list` THEN
   META_EXISTS_TAC THEN
   REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS; fst exec] THEN
   REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
   FULL_INIT_TAC THEN KP4_INPUT_TAC p THEN
   MAP_EVERY (fun n ->
     ARM_STEPS_TAC exec [n] THEN INLINE_W1P2_FIX_TAC THEN INLINE_W1P2_SIMP_TAC)
    (1--nsteps) THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
   REPEAT CONJ_TAC THEN
   W(fun (_,w) -> if KP4_IS_BYTES w then KP4_BYTES_TAC
                  else DISCHARGE_SAFETY_PROPERTY_TAC));;

(*** The three regions: after the first call (nonces 7 to 10, s2 2 to 5),  ***)
(*** the second (4, 5, 6: s1 4, s2 0 and 1; the fourth output, nonce 255,   ***)
(*** is not packed) and the third (0 to 3, s1 0 to 3). The pointers that    ***)
(*** the code keeps in X21 to X28 into the first polynomial buffer are set  ***)
(*** in one region and used in the next.                                    ***)

let KP65_A =
  { k4_st = 0x10f7c; k4_en = 0x11a2c;
    k4_polys = [192,1024; 1216,1152; 2240,1280; 3264,1408];
    k4_pre = "read X21 s = word_add fp (word 3264) /\\
              read X22 s = word_add fp (word 192) /\\
              read X25 s = word_add fp (word 1216) /\\
              read X28 s = word_add fp (word 2240) /\\";
    k4_post = "read X0 s = word_add fp (word 4288) /\\
               read X1 s = word_add fp (word 192) /\\
               read X2 s = word_add fp (word 1216) /\\
               read X3 s = word_add fp (word 2240) /\\
               read X4 s = word_add fp (word 5472) /\\
               read X5 s = word 4 /\\ read X6 s = word 5 /\\ read X7 s = word 6 /\\
               read X23 s = word_add fp (word 224) /\\
               read X28 s = word_add fp (word 4288) /\\
               read (memory :> bytes8 fp) s = word 255 /\\";
    k4_regs = "X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X23; X28";
    k4_stores = [0,1; 16,160; 5568,8] };;

let KP65_B =
  { k4_st = 0x11a30; k4_en = 0x12278;
    k4_polys = [4288,640; 192,768; 1216,896];
    k4_pre = "read X22 s = word_add fp (word 192) /\\
              read X23 s = word_add fp (word 224) /\\
              read X28 s = word_add fp (word 4288) /\\";
    k4_post = "read X0 s = word_add fp (word 192) /\\
               read X1 s = word_add fp (word 1216) /\\
               read X2 s = word_add fp (word 2240) /\\
               read X3 s = word_add fp (word 3264) /\\
               read X4 s = word_add fp (word 5472) /\\
               read X5 s = word 0 /\\ read X6 s = word 1 /\\ read X7 s = word 2 /\\
               read X21 s = word_add fp (word 448) /\\
               read X24 s = word_add fp (word 576) /\\
               read X25 s = word_add fp (word 608) /\\
               read X26 s = word_add fp (word 640) /\\
               read X27 s = word_add fp (word 672) /\\
               read X28 s = word_add fp (word 480) /\\
               read (memory :> bytes8 fp) s = word 3 /\\";
    k4_regs = "X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X21; X24; X25; X26; X27; X28";
    k4_stores = [0,1; 16,160; 5568,8] };;

let KP65_C =
  { k4_st = 0x1227c; k4_en = 0x12cdc;
    k4_polys = [192,128; 1216,256; 2240,384; 3264,512];
    k4_pre = "read X21 s = word_add fp (word 448) /\\
              read X22 s = word_add fp (word 192) /\\
              read X23 s = word_add fp (word 224) /\\
              read X24 s = word_add fp (word 576) /\\
              read X25 s = word_add fp (word 608) /\\
              read X26 s = word_add fp (word 640) /\\
              read X27 s = word_add fp (word 672) /\\
              read X28 s = word_add fp (word 480) /\\";
    k4_post = "read X0 s = word_add fp (word 192) /\\";
    k4_regs = "X0; X8";
    k4_stores = [16,176; 5568,8] };;

let KP65_REGIONS = [KP65_A; KP65_B; KP65_C];;

(* ------------------------------------------------------------------------- *)
(* The lemmas.                                                               *)
(* ------------------------------------------------------------------------- *)

let KI65_SEED = KI65_SEED_PROVE ();;

let KI65_PACK_THS = map KP_PACK4_PROVE KP65_REGIONS;;

let KI65_SHAKE = KG_SHAKE_PROVE KI_SHAKE65_INST "X20";;
