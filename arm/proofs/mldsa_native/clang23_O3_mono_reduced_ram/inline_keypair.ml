(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Region lemmas for the code that clang 23 -O3 has inlined into             *)
(* mldsa{44,87}_keypair_internal of the monolithic reduced-RAM build:        *)
(*                                                                           *)
(* - the packing of the polynomials of s1 and s2 into the secret key        *)
(*   (eta = 2, mldsa_polyeta_pack): for each polynomial a loop of two        *)
(*   iterations of 128 coefficients, which gathers the 32-bit coefficients   *)
(*   into vectors (LDP and LD1 of S lanes), takes their low bytes with TBL   *)
(*   (the index vector 0x3c38..0400 of the image, kept in Q15 and on the     *)
(*   stack), computes 2 - c bytewise, shifts and ORs the 3-bit values and    *)
(*   stores 48 bytes with ST3; between the loops the code zeroes a slot of   *)
(*   the stack (the mld_zeroize of the C function). A region, from the       *)
(*   instruction after the previous loop (or call) to the instruction after  *)
(*   its own loop, is simulated with the two iterations unrolled,            *)
(*   normalizing the vector registers after each step as in inline_cpt.ml,   *)
(*   and each of the 96 stored bytes is proved equal to mld_polyeta_pack_2   *)
(*   by a bit-blast with the coefficients as variables (KP_PACK2_TERM,       *)
(*   KP_PACK2_PROVE);                                                        *)
(* - the SHAKE256 of the public key into tr (instances of KG_SHAKE_PROVE of  *)
(*   inline_keygen_shake.ml);                                                *)
(* - the SHAKE256 of the seed extended by k and l, which absorbs one block   *)
(*   (KI_SEED_TERM, KI_SEED_PROVE).                                          *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_cpt.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_eta4.ml";;

(*** Byte k of the interleaving of three vectors of bytes ***)

let KP_EL3 = prove
 (`!a b c:A. EL 0 [a;b;c] = a /\ EL 1 [a;b;c] = b /\ EL 2 [a;b;c] = c`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV num_CONV) THEN
  REWRITE_TAC[EL; HD; TL]);;

let KP_ILV3 = map (fun k ->
  let tm = subst [mk_small_numeral(8 * k),`p:num`;
                  mk_small_numeral(8 * (k / 3)),`q:num`]
    (subst [List.nth [`x1:int128`;`x2:int128`;`x3:int128`] (k mod 3),`y:int128`]
      `word_subword (word_interleave 8 [x1:int128;x2;x3]:384 word) (p,8):byte =
       word_subword (y:int128) (q,8)`) in
  prove(tm,
    REWRITE_TAC[word_interleave] THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_OF_BITS; BIT_WORD_SUBWORD;
                IN_ELIM_THM; DIMINDEX_8; DIMINDEX_128;
                DIMINDEX_CONV `dimindex(:384)`] THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    REWRITE_TAC[BIT_WORD_OF_BITS; IN_ELIM_THM; DIMINDEX_CONV `dimindex(:384)`;
                LET_DEF; LET_END_DEF; LENGTH; MIN] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[KP_EL3] THEN
    CONV_TAC NUM_REDUCE_CONV)) (0--47);;

(*** The ST3 stores at sk + k (three 128-bit stores of subwords of the    ***)
(*** interleaving) as facts about their bytes                            ***)

let KP_ST3_SPLIT_TAC (base:term) =
  let isilv t = try fst(dest_const t) = "word_interleave" with Failure _ -> false in
  WIDE_STORE_SPLIT_TAC base 8 THEN
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_eq c && free_in base (lhand c) &&
       can (term_match [] `read (memory :> bytes8 a) s = x`) c &&
       can (find_term isilv) (rand c)
    then CONV_RULE(RAND_CONV(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                             REWRITE_CONV KP_ILV3 THENC
                             DEPTH_CONV CPT_OOR_CONV THENC CPT_EXTRACT_CONV)) th
    else th);;

(*** The 256 coefficients at sp + off as 256 facts with numeral offsets ***)

let KP_IN_TAC chunks off =
  let pat = subst [mk_small_numeral off,`OFF:num`]
    `!i. i < 256 ==> read (memory :> bytes32 (word_add sp (word (OFF + 4 * i)))) s0 =
                     (x:num->int32) i` in
  FIRST_ASSUM(fun th ->
    if concl th <> pat then NO_TAC else
    let ths = map (fun i ->
      let th1 = MP (SPEC (mk_small_numeral i) th)
                   (EQT_ELIM(NUM_REDUCE_CONV(mk_binary "<" (mk_small_numeral i,`256`)))) in
      CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV) th1) (0--255) in
    let conv = REWRITE_CONV[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);
                            el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);
                            PTR_ADD_G; GSYM ADD_ASSOC] THENC
               DEPTH_CONV NUM_ADD_CONV in
    let chunk m =
      let lhs = parse_term(Printf.sprintf
        "read (memory :> bytes128 (word_add sp (word %d))) s0" (off + 16 * m)) in
      REWRITE_RULE ths (conv lhs) in
    MAP_EVERY ASSUME_TAC (ths @ (if chunks then map chunk (0--63) else [])));;

(*** One byte of the output against the specification ***)

let KP_PACK2_BYTE_TAC =
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  W(fun (asl,w) ->
    let l = lhand w in
    FIRST_ASSUM(fun th -> if lhand(concl th) = l then GEN_REWRITE_TAC LAND_CONV [th]
                          else NO_TAC)) THEN
  REWRITE_TAC[mld_polyeta_pack_2] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  APP_BLAST_TAC `x:num->int32`;;

(* ------------------------------------------------------------------------- *)
(* The statement of a region [st, en) of the image that packs the 256        *)
(* coefficients x at sp + inofs into the 96 bytes at sk + outofs (sk in      *)
(* X19), with                                                                *)
(*   pre     extra facts about the state before, each followed by /\         *)
(*   post    extra facts about the state after, each followed by /\          *)
(*   mayregs the X registers that change, after PC                           *)
(*   stores  the ranges (offset, size) from sp that the region writes        *)
(*   reads   the other ranges from sp that it reads                          *)
(*   consts  whether it loads the index vector from the image                *)
(* ------------------------------------------------------------------------- *)

let KP_IDX = "word 0x3c3834302c2824201c1814100c080400:int128";;

let KP_PACK2_TERM fn st en inofs outofs (pre:string) (post:string)
                  (mayregs:string) (stores:(int*int) list) (reads:(int*int) list)
                  (consts:bool) =
  let ss = Printf.sprintf in
  let rng (ofs,n) = ss "word_add sp (word %d),%d" ofs n in
  let nov = String.concat "" (map (fun r ->
      ss "      nonoverlapping (%s) (word pc,libmldsa_size) /\\\n      nonoverlapping (%s) (word_add sk (word %d),96) /\\\n"
        (rng r) (rng r) outofs) stores) in
  let novr = String.concat "" (map (fun r ->
      ss "      nonoverlapping (%s) (word_add sk (word %d),96) /\\\n" (rng r) outofs) reads) in
  let racc = String.concat "" (map (fun r -> "; " ^ rng r) (reads @ stores)) ^
             (if consts then ss "; word(pc + %s_consts),16" fn else "") in
  let wacc = String.concat "" (map (fun r -> "; " ^ rng r) stores) in
  let smem = String.concat "" (map (fun r -> ";\n                       memory :> bytes(" ^ rng r ^ ")") stores) in
  parse_term(ss
 "exists f_events.
    forall e (sk:int64) (sp:int64) (x:num->int32) pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 16 sp /\\
      nonoverlapping (word_add sk (word %d),96) (word pc,libmldsa_size) /\\
      nonoverlapping (word_add sk (word %d),96) (word_add sp (word %d),1024) /\\
%s%s      T
      ==> ensures arm
           (\\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read PC s = word (pc + %d) /\\
                read SP s = sp /\\ read X19 s = sk /\\ %s
                (!i. i < 256
                     ==> read (memory :> bytes32 (word_add sp (word (%d + 4 * i)))) s =
                         x i) /\\
                read events s = e)
           (\\s. read PC s = word (pc + %d) /\\ %s
                (!j. j < 96
                     ==> read (memory :> bytes8 (word_add sk (word (%d + j)))) s =
                         mld_polyeta_pack_2 x j) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events sk sp pc /\\
                   memaccess_inbounds e2 [word_add sp (word %d),1024%s]
                    [word_add sk (word %d),96%s]))
           (MAYCHANGE [PC; %s] ,,
            MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12;
                       Q13; Q14; Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23;
                       Q24; Q25; Q26; Q27; Q28; Q29; Q30; Q31] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(word_add sk (word %d),96)%s])"
  outofs outofs inofs nov novr
  st pre inofs
  en post outofs inofs racc outofs wacc
  mayregs outofs smem);;

(*** The proof: simulate the nsteps steps (an ADRP at the steps adrps),     ***)
(*** normalizing after each, then the 96 bytes against the specification    ***)

let KP_PACK2_PROVE fn exec tm inofs adrps chunks nsteps =
  let lam = `\(sk:int64) (sp:int64) (pc:num). f_ev_kp sk sp pc :(uarch_event)list` in
  let cth = MLDSA_NATIVE_IMAGE_CONST_RULE (layout (fn ^ "_consts")) 128 in
  prove(tm,
   CONCRETIZE_F_EVENTS_TAC lam THEN
   META_EXISTS_TAC THEN
   REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS; fst exec] THEN
   REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
   FULL_INIT_TAC THEN
   (if adrps = [] then ALL_TAC else
    FIRST_ASSUM(fun ath -> try ASSUME_TAC(MATCH_MP cth ath) with Failure _ -> NO_TAC)) THEN
   KP_IN_TAC chunks inofs THEN
   MAP_EVERY (fun n ->
     ARM_STEPS_TAC exec [n] THEN
     (if mem n adrps then MLKEM_NATIVE_ADRP_TAC else ALL_TAC) THEN
     CPT_STEP_NORM_TAC n) (1--nsteps) THEN
   KP_ST3_SPLIT_TAC `sk:int64` THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
   REPEAT CONJ_TAC THEN
   TRY(CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THEN KP_PACK2_BYTE_TAC THEN NO_TAC) THEN
   TRY(DISCHARGE_SAFETY_PROPERTY_TAC THEN NO_TAC));;

(* ------------------------------------------------------------------------- *)
(* mldsa44_keypair_internal: the eight packings. The first four (after the   *)
(* first call of poly_uniform_eta_4x, nonces 4 to 7) are s2 into sk + 512 + *)
(* 96 k, the last four (nonces 0 to 3) s1 into sk + 128 + 96 k, from the     *)
(* polynomials at sp + 32 + 1024 k. The first loads the index vector from    *)
(* the image into Q15, the fourth spills it to sp + 16, and the last four    *)
(* reload it from there; the last three take the address of their input      *)
(* from X25, X24 and X23 (sp + 1056 + 1024 (k - 1)).                         *)
(* ------------------------------------------------------------------------- *)

let KP44_PACK_REGIONS =
  [(0x11f8,0x1210,0x1600); (0x1600,0x161c,0x1a24); (0x1a24,0x1a40,0x1e48);
   (0x1e48,0x1e6c,0x2274); (0x22ac,0x22c4,0x26ac); (0x26ac,0x26c8,0x2ad0);
   (0x2ad0,0x2aec,0x2ef4); (0x2ef4,0x2f10,0x3318)];;

let KP44_PACK_X22 = "read X22 s = word_add sp (word 32) /\\";;
let KP44_PACK_Q15 = "read Q15 s = " ^ KP_IDX ^ " /\\";;
let KP44_PACK_SLOT = "read (memory :> bytes128 (word_add sp (word 16))) s = " ^ KP_IDX ^ " /\\";;

let KP44_PACK_PARAMS k =
  let inofs = 32 + 1024 * (k mod 4) in
  let outofs = if k < 4 then 512 + 96 * k else 128 + 96 * (k - 4) in
  let ptr = ["X25";"X24";"X23"] in
  let pre, post, regs, stores, reads, consts =
    match k with
      0 -> KP44_PACK_X22, KP44_PACK_Q15, "X0; X8; X9; X10; X11; X12; X13; X14; X15; X16; X17; X18",
           [], [], true
    | 1 | 2 -> KP44_PACK_X22 ^ KP44_PACK_Q15, KP44_PACK_Q15,
           "X0; X1; X2; X8; X9; X10; X11; X12; X13; X14; X15; X16; X17; X18",
           [(4384,8)], [], false
    | 3 -> KP44_PACK_X22 ^ KP44_PACK_Q15, KP44_PACK_SLOT,
           "X0; X1; X2; X8; X9; X10; X11; X12; X13; X14; X15; X16; X17; X18",
           [(16,16); (4384,8)], [], false
    | 4 -> KP44_PACK_SLOT, "",
           "X0; X8; X9; X10; X11; X12; X13; X14; X15; X16; X17; X18",
           [], [(16,16)], false
    | _ -> let r = List.nth ptr (k - 5) in
           Printf.sprintf "read %s s = word_add sp (word %d) /\\ " r inofs ^ KP44_PACK_SLOT, "",
           "X0; X1; X8; X9; X10; X11; X12; X13; X14; X15; X16; X17; X18; " ^ r,
           [(4384,8)], [(16,16)], false in
  (inofs, outofs, pre, post, regs, stores, reads, consts);;

let KP44_PACK_TERM k =
  let (st,_,en) = List.nth KP44_PACK_REGIONS k in
  let (inofs,outofs,pre,post,regs,stores,reads,consts) = KP44_PACK_PARAMS k in
  KP_PACK2_TERM "mldsa44_keypair_internal" st en inofs outofs pre post regs
   stores reads consts;;

let KP44_PACK k =
  let (st,hd,en) = List.nth KP44_PACK_REGIONS k in
  let (inofs,_,_,_,_,_,_,consts) = KP44_PACK_PARAMS k in
  let exec = INLINE_LOOP_EXEC (string_of_int st) (string_of_int en) in
  let nsteps = (hd - st) / 4 + 2 * ((en - hd) / 4) in
  KP_PACK2_PROVE "mldsa44_keypair_internal" exec (KP44_PACK_TERM k) inofs
   (if consts then [3] else []) false nsteps;;

(* ------------------------------------------------------------------------- *)
(* mldsa87_keypair_internal: the fifteen packings, with the polynomials at   *)
(* sp + 352 + 1024 k (the third batch at sp + 4448 + 1024 k), the index      *)
(* vector spilled to sp + 336, the slot of the zeroing at sp + 7776. The     *)
(* first two batches (nonces 11 to 14 and 7 to 10) are s2 into             *)
(* sk + 1184 + 96 k and sk + 800 + 96 k, the last two (nonces 4 to 6 and 0  *)
(* to 3) s1 into sk + 512 + 96 k and sk + 128 + 96 k. The packings of the   *)
(* third batch are compiled differently (the index vector in Q18, the       *)
(* output offset carried in X9 from one loop to the next).                  *)
(* ------------------------------------------------------------------------- *)

let KP87_PACK_REGIONS =
  [(0x237c0,0x237d8,0x23bc8); (0x23bc8,0x23be4,0x23fec); (0x23fec,0x24008,0x24410);
   (0x24410,0x24434,0x2483c); (0x24874,0x2488c,0x24c74); (0x24c74,0x24c94,0x2509c);
   (0x2509c,0x250bc,0x254c4); (0x254c4,0x254e4,0x258ec); (0x25930,0x25938,0x25e40);
   (0x25e40,0x25e54,0x2635c); (0x2635c,0x26370,0x26878); (0x268b0,0x268c8,0x26cb0);
   (0x26cb0,0x26ccc,0x270d4); (0x270d4,0x270f0,0x274f8); (0x274f8,0x27514,0x2791c)];;

let KP87_PACK_X22 = "read X22 s = word_add sp (word 352) /\\";;
let KP87_PACK_SLOT = "read (memory :> bytes128 (word_add sp (word 336))) s = " ^ KP_IDX ^ " /\\";;

let KP87_PACK_PARAMS k =
  let r0 = "X0; X8; X9; X10; X11; X12; X13; X14; X15; X16; X17; X18"
  and r1 = "X0; X1; X2; X8; X9; X10; X11; X12; X13; X14; X15; X16; X17; X18"
  and r8 = "X0; X1; X2; X3; X4; X5; X8; X9; X10; X11; X12; X13; X14; X15; X16; X17; X18" in
  let ins = [352;1376;2400;3424; 352;1376;2400;3424; 4448;5472;6496; 352;1376;2400;3424] in
  let outs = [1184;1280;1376;1472; 800;896;992;1088; 512;608;704; 128;224;320;416] in
  let inofs = List.nth ins k and outofs = List.nth outs k in
  let x9 n = Printf.sprintf "read X9 s = word %d /\\ " n in
  let pre, post, regs, stores, reads, consts =
    match k with
      0 -> KP87_PACK_X22, KP44_PACK_Q15, r0, [], [], true
    | 1 | 2 -> KP87_PACK_X22 ^ KP44_PACK_Q15, KP44_PACK_Q15, r1, [(7776,8)], [], false
    | 3 -> KP87_PACK_X22 ^ KP44_PACK_Q15, KP87_PACK_SLOT, r1,
           [(336,16); (7776,8)], [], false
    | 4 | 11 -> KP87_PACK_SLOT, "", r0, [], [(336,16)], false
    | 5 | 6 | 7 -> KP87_PACK_X22 ^ KP87_PACK_SLOT, "", r1, [(7776,8)], [(336,16)], false
    | 8 -> "read X27 s = word_add sp (word 352) /\\ " ^ KP87_PACK_SLOT, x9 608, r8,
           [(16,320)], [(336,16)], false
    | 9 -> x9 608 ^ KP87_PACK_SLOT, x9 704, r8, [(16,320); (7776,8)], [(336,16)], false
    | 10 -> x9 704 ^ KP87_PACK_SLOT, "", r8, [(16,320); (7776,8)], [(336,16)], false
    | _ -> let r = List.nth ["X25";"X24";"X23"] (k - 12) in
           Printf.sprintf "read %s s = word_add sp (word %d) /\\ " r inofs ^ KP87_PACK_SLOT, "",
           "X0; X1; X8; X9; X10; X11; X12; X13; X14; X15; X16; X17; X18; " ^ r,
           [(7776,8)], [(336,16)], false in
  (inofs, outofs, pre, post, regs, stores, reads, consts);;

let KP87_PACK_TERM k =
  let (st,_,en) = List.nth KP87_PACK_REGIONS k in
  let (inofs,outofs,pre,post,regs,stores,reads,consts) = KP87_PACK_PARAMS k in
  KP_PACK2_TERM "mldsa87_keypair_internal" st en inofs outofs pre post regs
   stores reads consts;;

let KP87_PACK k =
  let (st,hd,en) = List.nth KP87_PACK_REGIONS k in
  let (inofs,_,_,_,_,_,_,consts) = KP87_PACK_PARAMS k in
  let exec = INLINE_LOOP_EXEC (string_of_int st) (string_of_int en) in
  let nsteps = (hd - st) / 4 + 2 * ((en - hd) / 4) in
  KP_PACK2_PROVE "mldsa87_keypair_internal" exec (KP87_PACK_TERM k) inofs
   (if consts then [3] else []) (8 <= k && k <= 10) nsteps;;

(* ------------------------------------------------------------------------- *)
(* The SHAKE256 of the public key into tr, inlined after the call of         *)
(* mld_compute_pack_t0_t1 (KG_SHAKE_PROVE of inline_keygen_shake.ml): pk in  *)
(* X20, the state at fp + 4384 (X21 points to it), tr at fp + 4128; the      *)
(* region ends before the last store of the zeroing of the state, with the   *)
(* arguments of the memset of the polynomials (fp + 32, 0, 4096) in X0 to    *)
(* X2.                                                                       *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_keygen_shake.ml";;

let KI_SHAKE44_INST =
  { sh_fn = "mldsa44_keypair_internal"; sh_start = "in_shake256_2";
    sh_stop = "in_pack_sk_rho_key_tr";
    sh_pklen = 1312; sh_a = 4384; sh_t = 4128;
    sh_vars = "";
    sh_pre = "read X21 s = st /\\";
    sh_post = "read X0 s = word_add fp (word 32) /\\ read X1 s = word 0 /\\
               read X2 s = word 4096 /\\";
    sh_reads = ""; sh_mods = "X18; X24; X30";
    sh_calls = [75;139;203;268;340;412;484;556;628;684];
    sh_last_bytes = (88--95) @ (128--135); sh_last_chunks = [];
    sh_pk128 = []; sh_split = []; sh_rebuild = [88;128]; sh_steps = 709 };;

(*** mldsa87: pk (2592 bytes) in X20, the state at fp + 7776, tr at fp + 7520 ***)

let KI_SHAKE87_INST =
  { sh_fn = "mldsa87_keypair_internal"; sh_start = "in_shake256_2";
    sh_stop = "in_pack_sk_rho_key_tr";
    sh_pklen = 2592; sh_a = 7776; sh_t = 7520;
    sh_vars = "";
    sh_pre = "read X21 s = st /\\";
    sh_post = "read X0 s = word_add fp (word 352) /\\ read X1 s = word 0 /\\
               read X2 s = word 7168 /\\";
    sh_reads = ""; sh_mods = "X18; X24; X30";
    sh_calls = [75;139;203;268;340;412;484;556;628;700;772;844;916;988;1060;
                1132;1204;1276;1348;1364];
    sh_last_bytes = (8--15) @ (128--135); sh_last_chunks = [];
    sh_pk128 = []; sh_split = []; sh_rebuild = [8;128]; sh_steps = 1389 };;

(*** mldsa65: pk (1952 bytes) in X20, the state at fp + 5568 (X8 and X21    ***)
(*** point to it; the region starts after the MOVI that zeroes Q18), tr at   ***)
(*** fp + 5312, the last block in 128-bit chunks as in pk_from_sk_65 (the  ***)
(*** lemma is in inline_keypair_65.ml)                                       ***)

let KI_SHAKE65_INST =
  { sh_fn = "mldsa65_keypair_internal"; sh_start = "in_shake256_2";
    sh_stop = "in_pack_sk_rho_key_tr";
    sh_pklen = 1952; sh_a = 5568; sh_t = 5312;
    sh_vars = "";
    sh_pre = "read Q18 s = word 0 /\\";
    sh_post = "read X0 s = word_add fp (word 192) /\\ read X1 s = word 0 /\\
               read X2 s = word 5120 /\\";
    sh_reads = ""; sh_mods = "X18; X21; X30";
    sh_calls = [76;140;204;269;341;413;485;557;629;701;773;845;917;989;1017];
    sh_last_bytes = (48--55) @ (128--135); sh_last_chunks = [0;16;32];
    sh_pk128 = [1904;1920;1936]; sh_split = [0;16;32]; sh_rebuild = [48;128];
    sh_steps = 1042 };;

(* ------------------------------------------------------------------------- *)
(* The SHAKE256 of the seed (32 bytes SEED at seed) extended by the bytes    *)
(* k = 4 and l = 4, from the ADRP after the probe of the stack to the call   *)
(* of poly_uniform_eta_4x: the code copies the seed to fp + 4192 and stores  *)
(* k, l after it, zeroes the state at fp + 4384, XORs the input and the      *)
(* padding (0x1F at byte 34, 0x80 at byte 135) into it, partly with byte     *)
(* and lane operations on the zeroed state, calls mldsa_keccakf1600_permute, *)
(* copies the first 128 bytes of the state to the seed buffer at fp + 4256   *)
(* (rho, rho', key), zeroes the state and sets up the arguments of the first *)
(* call of poly_uniform_eta_4x (the polynomials at fp + 32 + 1024 k, rho' at *)
(* fp + 4288, the nonces 4 to 7). The canary is stored at fp + 4600.         *)
(*                                                                           *)
(* The proof gives the bytes of the seed as bytes of word SEED, splits the   *)
(* stores that later loads read in parts (KS_SPLIT_TAC), assembles the       *)
(* state from its pieces (KS_CHAIN_TAC, as PU_CHAIN_TAC of                   *)
(* inline_uniform_main.ml) and relates it and the output to                  *)
(* mld_shake256_state and mld_shake256_byte (KS_STATE_EQ, KS_OUT_EQ).        *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/utils/mldsa_native_sampling.ml";;


(*** The input of 34 bytes: the seed and the bytes k, l ***)

let KS_SEED_BYTE = prove
 (`!SEED j. SEED < 2 EXP 256 /\ j < 32
          ==> word((SEED DIV 2 EXP (8 * j)) MOD 256):byte =
              word_subword (word SEED:256 word) (8 * j,8)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; VAL_WORD_SUBWORD; DIMINDEX_8] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  SUBGOAL_THEN `SEED MOD 2 EXP 256 = SEED` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MIN; LE_REFL; MOD_MOD_REFL; ARITH_RULE `2 EXP 8 = 256`]);;

(*** The bytes of the seed in memory as bytes of word SEED ***)

let KS_SEED_HYP = `!j. j < 32 ==> read (memory :> bytes8 (word_add seed (word j))) s0 =
                       word_subword (word SEED:256 word) (8 * j,8)`;;

let KS_SEED_BYTES_TAC =
  FIRST_ASSUM(fun th ->
    if concl th <> `read (memory :> bytes(seed,32)) s0 = SEED` then NO_TAC else
    MP_TAC(ISPECL [`seed:int64`; `32`; `read memory (s0:armstate)`] READ_BYTES_BOUND) THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; th; ARITH_RULE `8 * 32 = 256`] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN KS_SEED_HYP ASSUME_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      MP_TAC(SPEC `j:num` (MATCH_MP MLD_READ_BYTES_BYTES8 th)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      MATCH_MP_TAC KS_SEED_BYTE THEN ASM_REWRITE_TAC[];
      ALL_TAC]);;

(*** The 16 bytes of the seed at offset k as a 128-bit load ***)

let KS_SEED_FACT k =
  let hth = ASSUME KS_SEED_HYP in
  let insts = map (fun i ->
    let j = k + i in
    let th = MP (SPEC (mk_small_numeral j) hth)
                (EQT_ELIM(NUM_REDUCE_CONV(mk_binary "<" (mk_small_numeral j,`32`)))) in
    CONV_RULE(DEPTH_CONV NUM_RED_CONV) (REWRITE_RULE[WORD_ADD_0] th)) (0--15) in
  let addr = if k = 0 then "seed" else Printf.sprintf "word_add seed (word %d)" k in
  let lhs = parse_term(Printf.sprintf "read (memory :> bytes128 (%s)) s0" addr) in
  let conv = REWRITE_CONV[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);
                          el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);
                          el 3 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);
                          el 4 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);
                          PTR_ADD_G; GSYM ADD_ASSOC] THENC
             DEPTH_CONV NUM_ADD_CONV in
  let th = conv lhs in
  PROVE_HYP hth (REWRITE_RULE (WORD_ADD_0 :: insts) th);;

let KS_SEED128_TAC =
  FIRST_ASSUM(fun hth ->
    if concl hth <> KS_SEED_HYP then NO_TAC else
    MAP_EVERY (fun k -> ASSUME_TAC(PROVE_HYP hth (KS_SEED_FACT k))) [0;16]);;

(*** Split a fact about a 128-bit or 16-bit store at fp + off (any value) ***)
(*** into facts about all its aligned parts, keeping the fact itself     ***)

let KS_UNSPLIT = CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT;;

let KS_SPLIT_RULE th =
  let rec split th =
    let l,_ = dest_eq(concl th) in
    let bnn = fst(dest_const(rator(rand(rand(rator l))))) in
    if bnn = "bytes8" then [th] else
    let k = assoc bnn ["bytes128",1; "bytes64",2; "bytes32",3; "bytes16",4] in
    let th1 = GEN_REWRITE_RULE I [el k KS_UNSPLIT] th in
    let th2 = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                        DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) th1 in
    th :: flat(map split (CONJUNCTS th2)) in
  tl(split th);;

let KS_SPLIT_TAC sname off sz =
  let s = mk_var(sname,`:armstate`) in
  let bn = "bytes" ^ string_of_int sz in
  let a = parse_term(Printf.sprintf "word_add fp (word %d):int64" off) in
  FIRST_ASSUM(fun th ->
    let c = concl th in
    try let l,r = dest_eq c in
        let comp = rand(rator l) in
        if rand l = s && fst(dest_const(rator(rand comp))) = bn && rand(rand comp) = a
        then MAP_EVERY ASSUME_TAC (KS_SPLIT_RULE th)
        else NO_TAC
    with Failure _ -> NO_TAC);;

let KS_BYTES_EXTEND = prove
 (`!d:int64 j k x s:armstate.
        read (memory :> bytes(d,j)) s = x MOD 2 EXP (8 * j) /\
        read (memory :> bytes(word_add d (word j),k)) s =
        (x DIV 2 EXP (8 * j)) MOD 2 EXP (8 * k)
        ==> read (memory :> bytes(d,j + k)) s = x MOD 2 EXP (8 * (j + k))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; MOD_MULT_MOD] THEN
  ARITH_TAC);;

let KS_B16 = prove(`!a:int64 s:armstate. read (memory :> bytes(a,16)) s = val(read (memory :> bytes128 a) s)`,
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES; DIMINDEX_128] THEN CONV_TAC NUM_REDUCE_CONV);;
let KS_B1 = prove(`!a:int64 s:armstate. read (memory :> bytes(a,1)) s = val(read (memory :> bytes8 a) s)`,
  REWRITE_TAC[READ_MEMORY_BYTES_BYTES8]);;

let KS_PIECE16 = prove
 (`!(S:1600 word) (A:int64) (s:armstate) (V:int128) off.
     read (memory :> bytes128 A) s = V /\ V = word_subword S (8 * off,128)
     ==> read (memory :> bytes(A,16)) s = (val S DIV 2 EXP (8 * off)) MOD 2 EXP 128`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[KS_B16] THEN ASM_REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_CONV `dimindex(:128)`; MIN; LE_REFL] THEN
  CONV_TAC NUM_REDUCE_CONV);;
let KS_PIECE8 = prove
 (`!(S:1600 word) (A:int64) (s:armstate) (V:byte) off.
     read (memory :> bytes8 A) s = V /\ V = word_subword S (8 * off,8)
     ==> read (memory :> bytes(A,1)) s = (val S DIV 2 EXP (8 * off)) MOD 2 EXP 8`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[KS_B1] THEN ASM_REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_CONV `dimindex(:8)`; MIN; LE_REFL] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let KS_NORMC = TRY_CONV(REWRITE_CONV[PTR_ADD_G]) THENC DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV);;
let KS_NORM = CONV_RULE KS_NORMC;;

(*** The state after the absorbing and padding, as a word ***)

(*** The parameters of an instance: the function, the region, the offset   ***)
(*** d of the buffers from those of mldsa44 (input fp + 4192 + d, seed      ***)
(*** buffer fp + 4256 + d, state fp + 4384 + d, canary fp + 4600 + d), the  ***)
(*** offset of the polynomials, k, l and the first nonce                     ***)

type kseed =
  { ks_fn : string; ks_st : int; ks_en : int; ks_d : int; ks_poly : int;
    ks_k : int; ks_l : int; ks_n0 : int };;

let KS_KL p = p.ks_k + 256 * p.ks_l;;

let KS_SW_OF kl =
  subst [mk_small_numeral kl,`kl:num`]
   `word_or (word_zx (word SEED:256 word):1600 word)
            (word(2 EXP 256 * kl + 2 EXP 272 * 31 + 2 EXP 1080 * 128))`;;

let KS_P34 = { KI_SHAKE44_INST with sh_pklen = 34 };;

let KS_STATE_EQ_RULE k l =
  let kl = k + 256 * l in
  let sub = [mk_small_numeral k,`k:num`; mk_small_numeral l,`l:num`;
             mk_small_numeral kl,`kl:num`] in
  let zxand = prove
   (subst sub `!w:256 word. word_and (word_zx w:1600 word) (word(2 EXP 256 * kl)) = word 0`,
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST) in
  prove
   (subst sub
     `!SEED. SEED < 2 EXP 256
             ==> mld_shake256_state 34 (SEED + 2 EXP 256 * (k + 256 * l)) =
                 word_or (word_zx (word SEED:256 word):1600 word)
                         (word(2 EXP 256 * kl + 2 EXP 272 * 31 + 2 EXP 1080 * 128))`,
    GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[INST [subst sub `SEED + 2 EXP 256 * (k + 256 * l)`,`PK:num`]
                     (SHAKE_STATE_EQ KS_P34)] THEN
    SUBGOAL_THEN
     (subst sub `word(((SEED + 2 EXP 256 * (k + 256 * l)) DIV 2 EXP 0) MOD 2 EXP 1088):1600 word =
                 word_add (word_zx (word SEED:256 word)) (word(2 EXP 256 * kl))`)
     SUBST1_TAC THENL
     [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ADD; VAL_WORD; VAL_WORD_ZX_GEN;
                  DIMINDEX_CONV `dimindex(:1600)`; DIMINDEX_CONV `dimindex(:256)`;
                  EXP; DIV_1] THEN
      SUBGOAL_THEN `SEED MOD 2 EXP 256 = SEED` SUBST1_TAC THENL
       [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN
       (subst sub `SEED + 2 EXP 256 * (k + 256 * l) < 2 EXP 1088 /\ SEED < 2 EXP 1600 /\
                   2 EXP 256 * kl < 2 EXP 1600 /\ SEED + 2 EXP 256 * kl < 2 EXP 1600 /\
                   SEED + 2 EXP 256 * (k + 256 * l) < 2 EXP 1600`)
       STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `SEED < 2 EXP 256` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[MOD_LT] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    REWRITE_TAC[MATCH_MP WORD_ADD_OR (SPEC `word SEED:256 word` zxand)] THEN
    SPEC_TAC(`word SEED:256 word`,`w:256 word`) THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC WORD_BLAST);;

let KS_OUT_EQ = prove
 (`!M. num_of_bytelist(list_of_seq (mld_shake256_byte 34 M) 128) =
       val(keccak_f1600 (mld_shake256_state 34 M)) MOD 2 EXP 1024`,
  GEN_TAC THEN
  MP_TAC(SPECL [`136`; `mld_shake256_state 34 M`; `136`; `0`; `1`; `0`; `128`]
               SQUEEZE_CHUNK) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; EXP; DIV_1; ETA_AX;
              ARITH_RULE `8 * 128 = 1024`] THEN
  REWRITE_TAC[GSYM mld_shake256_byte] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[num_CONV `1`; keccak_squeeze]);;

(*** The pieces of the state at fp + base, and the chain of them ***)

let KS_PIECES =
  [0,16; 16,16] @ map (fun j -> j,1) (32--39) @
  map (fun j -> j,16) [40;56;72;88;104] @ map (fun j -> j,1) (120--135) @
  map (fun j -> j,16) [136;152;168;184];;

let KS_PIECE_THM sw base asl sn off len =
  let sz,lem = if len = 16 then "bytes128",KS_PIECE16 else "bytes8",KS_PIECE8 in
  let ftm = parse_term(Printf.sprintf "read (memory :> %s (word_add fp (word %d))) %s" sz (base + off) sn) in
  let fact = snd(find (fun (_,th) -> let c = concl th in is_eq c && lhs c = ftm) asl) in
  let v = rhs(concl fact) in
  let a = parse_term(Printf.sprintf "word_add fp (word %d):int64" (base + off)) in
  let s = mk_var(sn,`:armstate`) in
  let inst = SPECL [sw; a; s; v; mk_small_numeral off] lem in
  let eqt = snd(dest_conj(fst(dest_imp(concl inst)))) in
  let eqth = prove(eqt, CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST) in
  MP inst (CONJ fact eqth);;

let KS_CHAIN_TAC p sn =
  let base = 4384 + p.ks_d and sw = KS_SW_OF (KS_KL p) in
  W(fun (asl,w) ->
    let s = mk_var(sn,`:armstate`) in
    let d = parse_term(Printf.sprintf "word_add fp (word %d):int64" base) in
    let x = mk_comb(`val:1600 word->num`,sw) in
    let cur0 = KS_NORM(prove(
      subst [s,`s:armstate`; x,`x:num`; d,`d:int64`]
       `read (memory :> bytes(d,0)) s = x MOD 2 EXP (8 * 0)`,
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; MULT_CLAUSES; EXP; MOD_1])) in
    let step (cur,j) (off,len) =
      assert (off = j);
      let pth = KS_NORM(KS_PIECE_THM sw base asl sn off len) in
      let ext = KS_NORM(SPECL [d; mk_small_numeral j; mk_small_numeral len; x; s] KS_BYTES_EXTEND) in
      (MP ext (CONJ cur pth), j + len) in
    let fin,n = rev_itlist (fun p st -> step st p) KS_PIECES (cur0,0) in
    ASSUME_TAC fin);;

(*** The chunks of the state after the permutation, and the output ***)

let KS_STATE_CHUNKS_TAC p sn =
  let s = mk_var(sn,`:armstate`) in
  let a = parse_term(Printf.sprintf "word_add fp (word %d):int64" (4384 + p.ks_d)) in
  let st = subst [s,`s:armstate`; a,`a:int64`] `read (memory :> wbytes (a:int64)) s :1600 word` in
  FIRST_ASSUM(fun th ->
    if not(is_eq(concl th) && lhs(concl th) = st) then NO_TAC else
    let sub = MATCH_MP SHAKE_WBYTES_SUB th in
    let mk k =
      let th1 = (CONJUNCT2 o CONJUNCT2)(SPEC (mk_small_numeral k) sub) in
      let th2 = MP th1 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th1)))) in
      CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC
                ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th2 in
    MAP_EVERY (fun k -> ASSUME_TAC(mk (16 * k))) (0--7));;

(*** The ORR of the address of the input buffer with 24 (fp 32-aligned) ***)

let KS_ORR24 d =
  let sub = [mk_small_numeral(4192 + d),`a:num`; mk_small_numeral(4216 + d),`b:num`] in
  prove
   (subst sub `!fp:int64. aligned 32 fp
        ==> word_or (word_add fp (word a)) (word 24) = word_add fp (word b)`,
    GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN (subst sub `word_and (word_add fp (word a):int64) (word 24) = word 0`)
     ASSUME_TAC THENL
     [SUBGOAL_THEN (subst sub `aligned 32 (word_add fp (word a):int64)`) MP_TAC THENL
       [CONV_TAC NORMALIZE_ALIGNED_WORD_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[ALIGNED_32_WORD_AND] THEN
      SPEC_TAC(subst sub `word_add fp (word a):int64`,`x:int64`) THEN CONV_TAC WORD_BLAST;
      ALL_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP WORD_ADD_OR th)]) THEN
    CONV_TAC WORD_RULE);;

let KS_ORR_TAC p =
  let th = KS_ORR24 p.ks_d in
  FIRST_ASSUM(fun ath ->
    if concl ath <> `aligned 32 (fp:int64)` then NO_TAC else
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP th ath]));;

let KS_MODLEMMA = prove(`!w:1600 word. val w MOD 2 EXP 1600 = val w`,
  GEN_TAC THEN MATCH_MP_TAC MOD_LT THEN MP_TAC(ISPEC `w:1600 word` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`]);;

(*** The 128 bytes of the seed buffer as the first bytes of the output ***)

let KS_OUT_TAC p sn =
  let s = mk_var(sn,`:armstate`) in
  let sw = KS_SW_OF (KS_KL p) in
  let steq = KS_STATE_EQ_RULE p.ks_k p.ks_l in
  REWRITE_TAC[KS_OUT_EQ] THEN
  FIRST_ASSUM(fun th -> if concl th = `SEED < 2 EXP 256`
                        then REWRITE_TAC[MATCH_MP steq th] else NO_TAC) THEN
  MP_TAC(SPECL [parse_term(Printf.sprintf "word_add fp (word %d):int64" (4256 + p.ks_d));
                mk_comb(`val:1600 word->num`,mk_comb(`keccak_f1600`,sw));
                `8`; s] VERIF_BYTES_OF_BYTES128) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[word_subword] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN SIMP_TAC[]];;

(*** The statement of the instance p ***)

let KI_SEED_TERM p =
  let d = p.ks_d and q = p.ks_poly in
  let fr = 4608 + d in
  parse_term(INLINE_FILL
 "exists f_events.
    forall e (fp:int64) (pk:int64) (sk:int64) (seed:int64) SEED guard canary pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 16 fp /\\ aligned 32 fp /\\
      nonoverlapping (word_sub fp (word 240),@FR240@) (word pc,libmldsa_size) /\\
      nonoverlapping (word_sub fp (word 240),@FR240@) (seed,32) /\\
      nonoverlapping (word_sub fp (word 240),@FR240@)
                     (word_add (word pc) (word got_stack_chk_guard),8) /\\
      nonoverlapping (word_sub fp (word 240),@FR240@) (guard,8)
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
                read X0 s = word_add fp (word @P0@) /\\
                read X1 s = word_add fp (word @P1@) /\\
                read X2 s = word_add fp (word @P2@) /\\
                read X3 s = word_add fp (word @P3@) /\\
                read X4 s = word_add fp (word @RP@) /\\
                read X5 s = word @N0@ /\\ read X6 s = word @N1@ /\\ read X7 s = word @N2@ /\\
                read X19 s = sk /\\ read X20 s = pk /\\
                read X21 s = word_add fp (word @STATE@) /\\
                read X22 s = word_add fp (word @P0@) /\\
                read X23 s = word_add fp (word @P3@) /\\
                read X24 s = word_add fp (word @P2@) /\\
                read X25 s = word_add fp (word @P1@) /\\
                read X26 s = word_add fp (word @BUF@) /\\
                read (memory :> bytes8 fp) s = word @N3@ /\\
                read (memory :> bytes64 (word_add fp (word @CAN@))) s = canary /\\
                read (memory :> bytes(word_add fp (word @BUF@),128)) s =
                  num_of_bytelist
                   (list_of_seq
                     (mld_shake256_byte 34 (SEED + 2 EXP 256 * (@K@ + 256 * @L@))) 128) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events seed guard pc fp /\\
                   memaccess_inbounds e2
                    [seed,32; word_sub fp (word 240),240; fp,@FR@;
                     word_add (word pc) (word got_stack_chk_guard),8; guard,8;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192]
                    [word_sub fp (word 240),240; fp,@FR@]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [X18; X19; X20; X21; X22; X23; X24; X25; X26; X30] ,,
            MAYCHANGE [memory :> bytes(word_sub fp (word 240),240);
                       memory :> bytes(fp,@FR@)])"
  (map (fun (k,v) -> k,string_of_int v)
    ["FR240",fr + 240; "FR",fr; "ST",p.ks_st; "EN",p.ks_en;
     "P0",q; "P1",q + 1024; "P2",q + 2048; "P3",q + 3072; "RP",4288 + d;
     "STATE",4384 + d; "BUF",4256 + d; "CAN",4600 + d;
     "N0",p.ks_n0; "N1",p.ks_n0 + 1; "N2",p.ks_n0 + 2; "N3",p.ks_n0 + 3;
     "K",p.ks_k; "L",p.ks_l]));;

let KI_SEED_PROVE p =
  let exec = ARM_MK_EXEC_RANGES_RULE
    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
    [(p.ks_st,p.ks_en); layout_range "mldsa_keccakf1600_permute"] in
  let d = p.ks_d in
  let sw = KS_SW_OF (KS_KL p) in
  let st = 4384 + d in
  prove(KI_SEED_TERM p,
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
   ARM_STEPS_TAC exec (2--20) THEN KS_ORR_TAC p THEN
   ARM_STEPS_TAC exec [21] THEN KS_SPLIT_TAC "s21" (st + 24) 128 THEN
   ARM_STEPS_TAC exec [22] THEN KS_SPLIT_TAC "s22" (4208 + d) 128 THEN
   ARM_STEPS_TAC exec (23--37) THEN KS_SPLIT_TAC "s37" (st + 120) 128 THEN
   ARM_STEPS_TAC exec (38--55) THEN KS_SPLIT_TAC "s55" (4224 + d) 16 THEN
   ARM_STEPS_TAC exec (56--77) THEN
   KS_CHAIN_TAC p "s77" THEN
   FIRST_ASSUM(fun th ->
     if can (term_match []
          (subst [mk_small_numeral st,`n:num`]
            `read (memory :> bytes(word_add fp (word n),200)) s77 = x`)) (concl th)
     then ASSUME_TAC(REWRITE_RULE[GSYM READ_MEMORY_WBYTES_1600]
            (CONV_RULE(RAND_CONV(REWRITE_CONV[ARITH_RULE `8 * 200 = 1600`;
                                              KS_MODLEMMA])) th))
     else NO_TAC) THEN
   ARM_STEPS_TAC exec [78] THEN
   FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc exec "H_PERM"
    [`read X0 s`; sw; `pc:num`; `read SP s`; `read X30 s`]
    [`seed:int64`; `guard:int64`; `pc:num`; `fp:int64`] 79 THEN
   KS_STATE_CHUNKS_TAC p "s79" THEN
   ARM_STEPS_TAC exec (80--124) THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL [KS_OUT_TAC p "s124"; DISCHARGE_SAFETY_PROPERTY_TAC]);;

let KS44 = { ks_fn = "mldsa44_keypair_internal"; ks_st = 0x1008; ks_en = 0x11f4;
             ks_d = 0; ks_poly = 32; ks_k = 4; ks_l = 4; ks_n0 = 4 };;

let KS87 = { ks_fn = "mldsa87_keypair_internal"; ks_st = 0x235d0; ks_en = 0x237bc;
             ks_d = 3392; ks_poly = 352; ks_k = 8; ks_l = 7; ks_n0 = 11 };;
