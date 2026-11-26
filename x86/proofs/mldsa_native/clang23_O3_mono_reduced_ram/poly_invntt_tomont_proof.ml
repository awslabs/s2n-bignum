(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Inverse NTT of the clang 23 -O3 build: the proof (see                     *)
(* poly_invntt_tomont_spec.ml). Layers 8 to 4 are scalar loops with a block  *)
(* per iteration: the index register starts below 0, so each loop has a      *)
(* lemma for its first iteration (from head to head) and one for the other   *)
(* iterations (intt_loops.ml). Layers 3 to 1 are the vectorised loops of     *)
(* poly_ntt with the inverse butterfly (ntt_loops.ml with ntt_inverse set),  *)
(* and a last loop scales each coefficient. The main proof goes through the  *)
(* loops with EVENTS_BIGSTEP_TAC; the code between them loads the constants  *)
(* and the pointer to the zetas of the next loop.                            *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_invntt_tomont_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/ntt_loops.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/intt_loops.ml";;

(* ------------------------------------------------------------------------- *)
(* The lemmas for the loops. Each is for the loop from its head to its exit, *)
(* with the events of the loop given by a function of its arguments.         *)
(* ------------------------------------------------------------------------- *)

ntt_fn_base () := 0x9150;;
ntt_inverse () := true;;

(*** The vectorised loops of layers 3 to 1: (head, exit, start, len, sign of z, instructions) ***)

let mldsa_intt_vec_params =
  [(0x850,0x99c,0,32,false,65); (0x9c0,0xaee,64,32,true,59);
   (0xb10,0xc3e,128,32,true,59); (0xc60,0xdac,192,32,false,65);
   (0xdd0,0xefe,0,64,true,59); (0xf20,0x104e,128,64,true,59);
   (0x1070,0x11bc,0,128,false,65)];;

let MLDSA_INTT_VEC_LOOPS =
  map (fun (k,(lo,eo,st,ln,zp,nb)) ->
    new_specification ["mldsa_intt_vec" ^ string_of_int k ^ "_events"]
      (prove_vec lo eo st ln zp nb))
   (zip (1--7) mldsa_intt_vec_params);;

(*** The scalar loops of layers 8 to 4: the first iteration and the others ***)

let mldsa_intt_scal_params =
  [{ ih = 0x20; ie = 0x72; im = 8; inn = 2; ic = 2; inb = 128 }, 21;
   { ih = 0x80; ie = 0x111; im = 7; inn = 4; ic = 4; inb = 64 }, 35;
   { ih = 0x120; ie = 0x227; im = 6; inn = 8; ic = 8; inb = 32 }, 63;
   { ih = 0x240; ie = 0x433; im = 5; inn = 16; ic = 16; inb = 16 }, 119;
   { ih = 0x450; ie = 0x823; im = 4; inn = 32; ic = 32; inb = 8 }, 231];;

let mldsa_intt_scal_lemmas k =
  let (lp,nb) = el (k - 1) mldsa_intt_scal_params in
  (* layer 4 keeps the zetas in RDX, the index in RSI and a + 124 in RCX *)
  (if k = 5 then (iz_reg () := "RDX"; ii_reg () := "RSI"; ib_off () := 124) else ());
  let f = new_specification ["mldsa_intt_first" ^ string_of_int k ^ "_events"] (prove_ifirst lp nb) in
  let l = new_specification ["mldsa_intt_loop" ^ string_of_int k ^ "_events"] (prove_iloop lp nb) in
  (iz_reg () := "RCX"; ii_reg () := "RDX"; ib_off () := 0);
  (f,l);;

let MLDSA_INTT_SCAL_1 = mldsa_intt_scal_lemmas 1;;
let MLDSA_INTT_SCAL_2 = mldsa_intt_scal_lemmas 2;;
let MLDSA_INTT_SCAL_3 = mldsa_intt_scal_lemmas 3;;
let MLDSA_INTT_SCAL_4 = mldsa_intt_scal_lemmas 4;;
let MLDSA_INTT_SCAL_5 = mldsa_intt_scal_lemmas 5;;
let MLDSA_INTT_SCAL_LOOPS =
  [MLDSA_INTT_SCAL_1; MLDSA_INTT_SCAL_2; MLDSA_INTT_SCAL_3; MLDSA_INTT_SCAL_4; MLDSA_INTT_SCAL_5];;

let MLDSA_INTT_SCALE_LOOP =
  new_specification ["mldsa_intt_scale_events"] (prove_iscale 0x11d0 0x1227 19);;

ntt_fn_base () := 0x7ab0;;
ntt_inverse () := false;;

(* ------------------------------------------------------------------------- *)
(* Tools for the main proof                                                  *)
(* ------------------------------------------------------------------------- *)

let INTT_MAIN_EXEC = MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;

let INTT_IMAGE_ZETAS = IMAGE_DATA_RULE_FOR mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc mld_zetas_data (layout "rodata_mld_zetas");;

let INTT_CONST_RULE = IMAGE_CONST_RULE_FOR mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc;;

(* the constant at the address ad loaded by the instruction that ends at the offset r from the function *)
let INTT_LOAD_CONST_TAC ad r = IMAGE_RIPREL_TAC (INTT_CONST_RULE ad 128) (0x9150 + r);;
let INTT_CONST_STEP ad r n = INTT_LOAD_CONST_TAC ad r THEN X86_STEPS_TAC INTT_MAIN_EXEC (n--n);;

let INTT_XMM_OF_YMM_TAC k =
  let ymm = Printf.sprintf "YMM%d" k in
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const(n,_)),st)),
           Comb(Comb(Const("word_join",_),_),v)) when n = ymm ->
        let xmm = mk_comb(mk_comb(`read:(x86state,int128)component->x86state->int128`,
                                 mk_const(Printf.sprintf "XMM%d" k,[])), st) in
        SUBGOAL_THEN (mk_eq(xmm,v)) ASSUME_TAC THENL
         [REWRITE_TAC[el k [XMM0;XMM1;XMM2;XMM3;XMM4]; READ_ZEROTOP_128] THEN
          ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST; ALL_TAC]
    | _ -> failwith "INTT_XMM_OF_YMM_TAC");;

(* the constants of a vectorised loop with the zeta -mld_zeta k, in the form of its lemma *)
let INTT_ZCONST k =
  let zk = mk_comb(`word_neg:int32->int32`,mk_comb(`mld_zeta`,mk_small_numeral k)) in
  let conv = REWRITE_CONV[mld_zeta; mld_zetas] THENC ONCE_DEPTH_CONV EL_CONV THENC DEPTH_CONV WORD_RED_CONV THENC DEPTH_CONV NUM_RED_CONV THENC REWRITE_CONV[] in
  let t3 = mk_comb(mk_comb(`word_join:int64->int64->int128`,mk_comb(`word_sx:int32->int64`,zk)),mk_comb(`word_sx:int32->int64`,zk)) in
  let q = mk_comb(mk_comb(`word_mul:int32->int32->int32`,zk),`word 58728449:int32`) in
  let zq = mk_comb(`word_zx:int32->int64`,q) in
  let t4 = mk_comb(mk_comb(`word_join:int64->int64->int128`,zq),zq) in
  (conv t3, conv t4);;

let INTT_ZSIGN k pos =
  let t = parse_term(Printf.sprintf (if pos then "&0 <= ival (word_neg (mld_zeta %d))" else "ival (word_neg (mld_zeta %d)) < &0") k) in
  EQT_ELIM((REWRITE_CONV[mld_zeta; mld_zetas] THENC ONCE_DEPTH_CONV EL_CONV THENC
            DEPTH_CONV WORD_RED_CONV THENC DEPTH_CONV INT_RED_CONV) t);;

let INTT_ZREWRITE j pos =
  let (c3,c4) = INTT_ZCONST j in
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM c3; GSYM c4]) THEN ASSUME_TAC(INTT_ZSIGN j pos);;

(* the pointer into mld_zetas loaded by an lea relative to RIP is the table at 152736 plus n *)
let INTT_RIPREL_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[RIPREL_ADDR_LEMMA; GSYM ADD_ASSOC]) THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV));;
let INTT_ZT_TAC n =
  SUBGOAL_THEN (parse_term(Printf.sprintf "word(pc + %d):int64 = word_add (word(pc + 152736)) (word %d)" (152736 + n) n)) ASSUME_TAC THENL
   [REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME(parse_term(Printf.sprintf "word(pc + %d):int64 = word_add (word(pc + 152736)) (word %d)" (152736 + n) n))]);;

let INTT_LAYERS_NEXT = prove(`!n y. mld_invntt_layers (n + 1) y = mld_invntt_blocks (8 - n) (2 EXP (7 - n)) (mld_invntt_layers n y)`,
  REWRITE_TAC[GSYM ADD1; mld_invntt_layers]);;
let INTT_BLOCKS_NEXT = prove(`!m b r. mld_invntt_blocks m (b + 1) r =
   mld_invntt_block (word_neg (mld_zeta (2 EXP m - 1 - b))) (2 * 2 EXP (8 - m) * b) (2 EXP (8 - m)) (mld_invntt_blocks m b r)`,
  REWRITE_TAC[GSYM ADD1; mld_invntt_blocks]);;
let INTT_LAYERS_EQ_INSTS =
  let red th = CONV_RULE(DEPTH_CONV NUM_RED_CONV) th in
  let ly n = red(SPECL [mk_small_numeral n; `y:num->int32`] INTT_LAYERS_NEXT) in
  let bl m b = red(SPECL [mk_small_numeral m; mk_small_numeral b; `r:num->int32`] INTT_BLOCKS_NEXT) in
  map ly (0--7) @ map (bl 3) (0--3) @ map (bl 2) [0;1] @ [bl 1 0];;
let INTT_LAYERS_EQ =
  let m8 = `mld_invntt_block (word_neg (mld_zeta 1)) 0 128 (mld_invntt_block (word_neg (mld_zeta 2)) 128 64 (mld_invntt_block (word_neg (mld_zeta 3)) 0 64 (mld_invntt_block (word_neg (mld_zeta 4)) 192 32 (mld_invntt_block (word_neg (mld_zeta 5)) 128 32 (mld_invntt_block (word_neg (mld_zeta 6)) 64 32 (mld_invntt_block (word_neg (mld_zeta 7)) 0 32 (mld_invntt_blocks 4 8 (mld_invntt_blocks 5 16 (mld_invntt_blocks 6 32 (mld_invntt_blocks 7 64 (mld_invntt_blocks 8 128 (x:num->int32))))))))))))` in
  prove(mk_eq(`mld_invntt_layers 8 (x:num->int32)`, m8),
    REWRITE_TAC(INTT_LAYERS_EQ_INSTS @ [mld_invntt_layers; mld_invntt_blocks]) THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV));;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together                     *)
(* ------------------------------------------------------------------------- *)
let MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  META_EXISTS_TAC THEN REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES; mld_poly_invntt_tomont; fst INTT_MAIN_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `nonoverlapping (a:int64,1024) (word(pc + rodata_mld_zetas),1024) /\
    nonoverlapping (a:int64,1024) (word(pc + mldsa_poly_invntt_tomont_consts),448) /\
    nonoverlapping (stackpointer:int64,8) (word(pc + rodata_mld_zetas),1024) /\
    nonoverlapping (stackpointer:int64,8) (word(pc + mldsa_poly_invntt_tomont_consts),448)`
  MP_TAC THENL [REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC; REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN STRIP_TAC] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  MAP_EVERY (fun k -> GHOST_INTRO_TAC (mk_var(Printf.sprintf "ymm%d_init" k, `:int256`)) (parse_term(Printf.sprintf "read YMM%d" k))) [0;1;2;3;4] THEN
  FULL_INIT_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLD_ZETAS_LOADED o MATCH_MP INTT_IMAGE_ZETAS o check (fun th -> can (term_match [] `bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc`) (concl th))) THEN
  X86_STEPS_TAC INTT_MAIN_EXEC (1--1) THEN
  X86_STEPS_TAC INTT_MAIN_EXEC (2--2) THEN INTT_RIPREL_TAC THEN INTT_ZT_TAC 1020 THEN
  X86_STEPS_TAC INTT_MAIN_EXEC (3--5) THEN
  EVENTS_BIGSTEP_TAC INTT_MAIN_EXEC (fst (el 0 MLDSA_INTT_SCAL_LOOPS)) [`a:int64`; `pc:num`; `word(pc + 152736):int64`; `x:num->int32`] 6 THEN
  EVENTS_BIGSTEP_TAC INTT_MAIN_EXEC (snd (el 0 MLDSA_INTT_SCAL_LOOPS)) [`a:int64`; `pc:num`; `word(pc + 152736):int64`; `x:num->int32`] 7 THEN
  X86_STEPS_TAC INTT_MAIN_EXEC (8--8) THEN INTT_RIPREL_TAC THEN INTT_ZT_TAC 508 THEN
  X86_STEPS_TAC INTT_MAIN_EXEC (9--9) THEN
  EVENTS_BIGSTEP_TAC INTT_MAIN_EXEC (fst (el 1 MLDSA_INTT_SCAL_LOOPS)) [`a:int64`; `pc:num`; `word(pc + 152736):int64`; `mld_invntt_blocks 8 128 x`] 10 THEN
  EVENTS_BIGSTEP_TAC INTT_MAIN_EXEC (snd (el 1 MLDSA_INTT_SCAL_LOOPS)) [`a:int64`; `pc:num`; `word(pc + 152736):int64`; `mld_invntt_blocks 8 128 x`] 11 THEN
  X86_STEPS_TAC INTT_MAIN_EXEC (12--12) THEN INTT_RIPREL_TAC THEN INTT_ZT_TAC 252 THEN
  X86_STEPS_TAC INTT_MAIN_EXEC (13--14) THEN
  EVENTS_BIGSTEP_TAC INTT_MAIN_EXEC (fst (el 2 MLDSA_INTT_SCAL_LOOPS)) [`a:int64`; `pc:num`; `word(pc + 152736):int64`; `mld_invntt_blocks 7 64 (mld_invntt_blocks 8 128 x)`] 15 THEN
  EVENTS_BIGSTEP_TAC INTT_MAIN_EXEC (snd (el 2 MLDSA_INTT_SCAL_LOOPS)) [`a:int64`; `pc:num`; `word(pc + 152736):int64`; `mld_invntt_blocks 7 64 (mld_invntt_blocks 8 128 x)`] 16 THEN
  X86_STEPS_TAC INTT_MAIN_EXEC (17--17) THEN INTT_RIPREL_TAC THEN INTT_ZT_TAC 124 THEN
  X86_STEPS_TAC INTT_MAIN_EXEC (18--19) THEN
  EVENTS_BIGSTEP_TAC INTT_MAIN_EXEC (fst (el 3 MLDSA_INTT_SCAL_LOOPS)) [`a:int64`; `pc:num`; `word(pc + 152736):int64`; `mld_invntt_blocks 6 32 (mld_invntt_blocks 7 64 (mld_invntt_blocks 8 128 x))`] 20 THEN
  EVENTS_BIGSTEP_TAC INTT_MAIN_EXEC (snd (el 3 MLDSA_INTT_SCAL_LOOPS)) [`a:int64`; `pc:num`; `word(pc + 152736):int64`; `mld_invntt_blocks 6 32 (mld_invntt_blocks 7 64 (mld_invntt_blocks 8 128 x))`] 21 THEN
  X86_STEPS_TAC INTT_MAIN_EXEC (22--23) THEN INTT_RIPREL_TAC THEN INTT_ZT_TAC 60 THEN
  X86_STEPS_TAC INTT_MAIN_EXEC (24--25) THEN
  EVENTS_BIGSTEP_TAC INTT_MAIN_EXEC (fst (el 4 MLDSA_INTT_SCAL_LOOPS)) [`a:int64`; `pc:num`; `word(pc + 152736):int64`; `mld_invntt_blocks 5 16 (mld_invntt_blocks 6 32 (mld_invntt_blocks 7 64 (mld_invntt_blocks 8 128 x)))`] 26 THEN
  EVENTS_BIGSTEP_TAC INTT_MAIN_EXEC (snd (el 4 MLDSA_INTT_SCAL_LOOPS)) [`a:int64`; `pc:num`; `word(pc + 152736):int64`; `mld_invntt_blocks 5 16 (mld_invntt_blocks 6 32 (mld_invntt_blocks 7 64 (mld_invntt_blocks 8 128 x)))`] 27 THEN
  X86_STEPS_TAC INTT_MAIN_EXEC (28--29) THEN
  INTT_CONST_STEP 0x251a0 0x836 30 THEN
  INTT_CONST_STEP 0x250d0 0x83e 31 THEN
  INTT_CONST_STEP 0x251b0 0x846 32 THEN
  INTT_CONST_STEP 0x250c0 0x84e 33 THEN
  X86_STEPS_TAC INTT_MAIN_EXEC (34--34) THEN
  MAP_EVERY INTT_XMM_OF_YMM_TAC [0;1;2] THEN
  MAP_EVERY INTT_XMM_OF_YMM_TAC [2;3;4] THEN
  INTT_ZREWRITE 7 false THEN
  EVENTS_BIGSTEP_TAC INTT_MAIN_EXEC (el 0 MLDSA_INTT_VEC_LOOPS) [`a:int64`; `pc:num`; `mld_invntt_blocks 4 8 (mld_invntt_blocks 5 16 (mld_invntt_blocks 6 32 (mld_invntt_blocks 7 64 (mld_invntt_blocks 8 128 x))))`; `word_neg (mld_zeta 7)`] 35 THEN
  X86_STEPS_TAC INTT_MAIN_EXEC (36--37) THEN
  INTT_CONST_STEP 0x251c0 0x9af 38 THEN
  INTT_CONST_STEP 0x251d0 0x9b7 39 THEN
  X86_STEPS_TAC INTT_MAIN_EXEC (40--40) THEN
  MAP_EVERY INTT_XMM_OF_YMM_TAC [2;3;4] THEN
  INTT_ZREWRITE 6 true THEN
  EVENTS_BIGSTEP_TAC INTT_MAIN_EXEC (el 1 MLDSA_INTT_VEC_LOOPS) [`a:int64`; `pc:num`; `mld_invntt_block (word_neg (mld_zeta 7)) 0 32 (mld_invntt_blocks 4 8 (mld_invntt_blocks 5 16 (mld_invntt_blocks 6 32 (mld_invntt_blocks 7 64 (mld_invntt_blocks 8 128 x)))))`; `word_neg (mld_zeta 6)`] 41 THEN
  X86_STEPS_TAC INTT_MAIN_EXEC (42--43) THEN
  INTT_CONST_STEP 0x251e0 0xb01 44 THEN
  INTT_CONST_STEP 0x251f0 0xb09 45 THEN
  X86_STEPS_TAC INTT_MAIN_EXEC (46--46) THEN
  MAP_EVERY INTT_XMM_OF_YMM_TAC [2;3;4] THEN
  INTT_ZREWRITE 5 true THEN
  EVENTS_BIGSTEP_TAC INTT_MAIN_EXEC (el 2 MLDSA_INTT_VEC_LOOPS) [`a:int64`; `pc:num`; `mld_invntt_block (word_neg (mld_zeta 6)) 64 32 (mld_invntt_block (word_neg (mld_zeta 7)) 0 32 (mld_invntt_blocks 4 8 (mld_invntt_blocks 5 16 (mld_invntt_blocks 6 32 (mld_invntt_blocks 7 64 (mld_invntt_blocks 8 128 x))))))`; `word_neg (mld_zeta 5)`] 47 THEN
  X86_STEPS_TAC INTT_MAIN_EXEC (48--49) THEN
  INTT_CONST_STEP 0x25200 0xc51 50 THEN
  INTT_CONST_STEP 0x25210 0xc59 51 THEN
  X86_STEPS_TAC INTT_MAIN_EXEC (52--52) THEN
  MAP_EVERY INTT_XMM_OF_YMM_TAC [2;3;4] THEN
  INTT_ZREWRITE 4 false THEN
  EVENTS_BIGSTEP_TAC INTT_MAIN_EXEC (el 3 MLDSA_INTT_VEC_LOOPS) [`a:int64`; `pc:num`; `mld_invntt_block (word_neg (mld_zeta 5)) 128 32 (mld_invntt_block (word_neg (mld_zeta 6)) 64 32 (mld_invntt_block (word_neg (mld_zeta 7)) 0 32 (mld_invntt_blocks 4 8 (mld_invntt_blocks 5 16 (mld_invntt_blocks 6 32 (mld_invntt_blocks 7 64 (mld_invntt_blocks 8 128 x)))))))`; `word_neg (mld_zeta 4)`] 53 THEN
  X86_STEPS_TAC INTT_MAIN_EXEC (54--55) THEN
  INTT_CONST_STEP 0x25220 0xdbf 56 THEN
  INTT_CONST_STEP 0x25230 0xdc7 57 THEN
  X86_STEPS_TAC INTT_MAIN_EXEC (58--58) THEN
  MAP_EVERY INTT_XMM_OF_YMM_TAC [2;3;4] THEN
  INTT_ZREWRITE 3 true THEN
  EVENTS_BIGSTEP_TAC INTT_MAIN_EXEC (el 4 MLDSA_INTT_VEC_LOOPS) [`a:int64`; `pc:num`; `mld_invntt_block (word_neg (mld_zeta 4)) 192 32 (mld_invntt_block (word_neg (mld_zeta 5)) 128 32 (mld_invntt_block (word_neg (mld_zeta 6)) 64 32 (mld_invntt_block (word_neg (mld_zeta 7)) 0 32 (mld_invntt_blocks 4 8 (mld_invntt_blocks 5 16 (mld_invntt_blocks 6 32 (mld_invntt_blocks 7 64 (mld_invntt_blocks 8 128 x))))))))`; `word_neg (mld_zeta 3)`] 59 THEN
  X86_STEPS_TAC INTT_MAIN_EXEC (60--61) THEN
  INTT_CONST_STEP 0x25240 0xf11 62 THEN
  INTT_CONST_STEP 0x25250 0xf19 63 THEN
  X86_STEPS_TAC INTT_MAIN_EXEC (64--64) THEN
  MAP_EVERY INTT_XMM_OF_YMM_TAC [2;3;4] THEN
  INTT_ZREWRITE 2 true THEN
  EVENTS_BIGSTEP_TAC INTT_MAIN_EXEC (el 5 MLDSA_INTT_VEC_LOOPS) [`a:int64`; `pc:num`; `mld_invntt_block (word_neg (mld_zeta 3)) 0 64 (mld_invntt_block (word_neg (mld_zeta 4)) 192 32 (mld_invntt_block (word_neg (mld_zeta 5)) 128 32 (mld_invntt_block (word_neg (mld_zeta 6)) 64 32 (mld_invntt_block (word_neg (mld_zeta 7)) 0 32 (mld_invntt_blocks 4 8 (mld_invntt_blocks 5 16 (mld_invntt_blocks 6 32 (mld_invntt_blocks 7 64 (mld_invntt_blocks 8 128 x)))))))))`; `word_neg (mld_zeta 2)`] 65 THEN
  X86_STEPS_TAC INTT_MAIN_EXEC (66--67) THEN
  INTT_CONST_STEP 0x25260 0x1061 68 THEN
  INTT_CONST_STEP 0x25270 0x1069 69 THEN
  X86_STEPS_TAC INTT_MAIN_EXEC (70--70) THEN
  MAP_EVERY INTT_XMM_OF_YMM_TAC [2;3;4] THEN
  INTT_ZREWRITE 1 false THEN
  EVENTS_BIGSTEP_TAC INTT_MAIN_EXEC (el 6 MLDSA_INTT_VEC_LOOPS) [`a:int64`; `pc:num`; `mld_invntt_block (word_neg (mld_zeta 2)) 128 64 (mld_invntt_block (word_neg (mld_zeta 3)) 0 64 (mld_invntt_block (word_neg (mld_zeta 4)) 192 32 (mld_invntt_block (word_neg (mld_zeta 5)) 128 32 (mld_invntt_block (word_neg (mld_zeta 6)) 64 32 (mld_invntt_block (word_neg (mld_zeta 7)) 0 32 (mld_invntt_blocks 4 8 (mld_invntt_blocks 5 16 (mld_invntt_blocks 6 32 (mld_invntt_blocks 7 64 (mld_invntt_blocks 8 128 x))))))))))`; `word_neg (mld_zeta 1)`] 71 THEN
  X86_STEPS_TAC INTT_MAIN_EXEC (72--74) THEN
  EVENTS_BIGSTEP_TAC INTT_MAIN_EXEC MLDSA_INTT_SCALE_LOOP [`a:int64`; `pc:num`; `mld_invntt_block (word_neg (mld_zeta 1)) 0 128 (mld_invntt_block (word_neg (mld_zeta 2)) 128 64 (mld_invntt_block (word_neg (mld_zeta 3)) 0 64 (mld_invntt_block (word_neg (mld_zeta 4)) 192 32 (mld_invntt_block (word_neg (mld_zeta 5)) 128 32 (mld_invntt_block (word_neg (mld_zeta 6)) 64 32 (mld_invntt_block (word_neg (mld_zeta 7)) 0 32 (mld_invntt_blocks 4 8 (mld_invntt_blocks 5 16 (mld_invntt_blocks 6 32 (mld_invntt_blocks 7 64 (mld_invntt_blocks 8 128 x)))))))))))`] 75 THEN
  X86_STEPS_TAC INTT_MAIN_EXEC (76--86) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[mld_poly_invntt_tomont; INTT_LAYERS_EQ] THEN ASM_REWRITE_TAC[] THEN
  EVENTS_APPEND_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;

