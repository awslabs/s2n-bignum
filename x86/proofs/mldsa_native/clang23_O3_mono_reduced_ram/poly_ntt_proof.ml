(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Forward NTT of the clang 23 -O3 build: the proof (see poly_ntt_spec.ml).  *)
(* clang has vectorised the layers 1 to 3 (one loop for each block, with the *)
(* zeta in a vector constant and the products by PMULUDQ), and unrolled the  *)
(* butterflies of layers 4 and 5 (a block per iteration), 6 and 7 (a block   *)
(* per iteration in scalar and SSE code) and 8 (one butterfly). The proof    *)
(* has a lemma for each of the 12 loops, from its head to its exit, in       *)
(* ntt_loops.ml (as generators), and the main proof goes through them one    *)
(* after the other with EVENTS_BIGSTEP_TAC; the code between the loops loads *)
(* the constants of the next one.                                            *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_ntt_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/ntt_loops.ml";;

(* ------------------------------------------------------------------------- *)
(* The lemmas for the 12 loops. Each is for the loop from its head to its    *)
(* exit, with the events of the loop given by a function of its arguments.   *)
(* ------------------------------------------------------------------------- *)

(*** The vectorised loops of layers 1 to 3: (head, exit, start, len, sign of z, instructions) ***)

let mldsa_ntt_vec_params =
  [(0x30,0x165,0,128,true,59); (0x180,0x2d3,0,64,false,65);
   (0x2f0,0x443,128,64,false,65); (0x460,0x595,0,32,true,59);
   (0x5b0,0x703,64,32,false,65); (0x720,0x873,128,32,false,65);
   (0x890,0x9c5,192,32,true,59)];;

let MLDSA_NTT_VEC_LOOPS =
  map (fun (k,(lo,eo,st,ln,zp,nb)) ->
    new_specification ["mldsa_ntt_vec" ^ string_of_int k ^ "_events"]
      (prove_vec lo eo st ln zp nb))
   (zip (1--7) mldsa_ntt_vec_params);;

(*** The loops of layers 4 and 5: pointer RDX biased to the end of the block ***)

let MLDSA_NTT_L4_LOOP =
  new_specification ["mldsa_ntt_l4_events"] (prove_scal 0x9e0 0xd53 3 32 124 8 229);;
let MLDSA_NTT_L5_LOOP =
  new_specification ["mldsa_ntt_l5_events"] (prove_scal 0xd60 0xf23 4 16 60 16 117);;

(*** The loops of layers 6 to 8: the index RDX counts the blocks (by 4 or 1) ***)

let MLDSA_NTT_L6_LOOP =
  new_specification ["mldsa_ntt_l6_events"]
    (prove_sc2 0xf30 0x1009 5 8 4 8 true (Some ("bytes128",2)) 45);;
let MLDSA_NTT_L7_LOOP =
  new_specification ["mldsa_ntt_l7_events"]
    (prove_sc2 0x1010 0x1099 6 4 4 4 true (Some ("bytes64",1)) 28);;
let MLDSA_NTT_L8_LOOP =
  new_specification ["mldsa_ntt_l8_events"]
    (prove_sc2 0x10a0 0x10ec 7 2 1 8 false None 18);;

(* ------------------------------------------------------------------------- *)
(* Tools for the main proof                                                   *)
(* ------------------------------------------------------------------------- *)

let NTT_MAIN_EXEC = MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;

let NTT_IMAGE_ZETAS = IMAGE_DATA_RULE_FOR mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc mld_zetas_data (layout "rodata_mld_zetas");;

let NTT_CONST_RULE = IMAGE_CONST_RULE_FOR mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc;;
(* the constant k (of the 16, from 0) loaded by the instruction that ends at the offset r from the function *)
let NTT_LOAD_CONST_TAC k r = IMAGE_RIPREL_TAC (NTT_CONST_RULE (0x250a0 + 16 * k) 128) (0x7ab0 + r);;

let NTT_XMM_OF_YMM_TAC k =
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
    | _ -> failwith "NTT_XMM_OF_YMM_TAC");;

(* the constants of loop k in the form of its lemma *)
let NTT_ZCONST k =
  let zk = mk_comb(`mld_zeta`,mk_small_numeral k) in
  let conv = REWRITE_CONV[mld_zeta; mld_zetas] THENC ONCE_DEPTH_CONV EL_CONV THENC DEPTH_CONV WORD_RED_CONV THENC DEPTH_CONV NUM_RED_CONV THENC REWRITE_CONV[] in
  let t3 = mk_comb(mk_comb(`word_join:int64->int64->int128`,mk_comb(`word_sx:int32->int64`,zk)),mk_comb(`word_sx:int32->int64`,zk)) in
  let q = mk_comb(mk_comb(`word_mul:int32->int32->int32`,zk),`word 58728449:int32`) in
  let zq = mk_comb(`word_zx:int32->int64`,q) in
  let t4 = mk_comb(mk_comb(`word_join:int64->int64->int128`,zq),zq) in
  (conv t3, conv t4);;

let NTT_ZSIGN k pos =
  let t = parse_term(Printf.sprintf (if pos then "&0 <= ival (mld_zeta %d)" else "ival (mld_zeta %d) < &0") k) in
  EQT_ELIM((REWRITE_CONV[mld_zeta; mld_zetas] THENC ONCE_DEPTH_CONV EL_CONV THENC
            DEPTH_CONV WORD_RED_CONV THENC DEPTH_CONV INT_RED_CONV) t);;


let NTT_CONST_STEP k r n = NTT_LOAD_CONST_TAC k r THEN X86_STEPS_TAC NTT_MAIN_EXEC (n--n);;

let NTT_ZREWRITE j pos =
  let (c3,c4) = NTT_ZCONST j in
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM c3; GSYM c4]) THEN ASSUME_TAC(NTT_ZSIGN j pos);;
let NTT_RIPREL_RCX_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[RIPREL_ADDR_LEMMA; GSYM ADD_ASSOC]) THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV));;

let NTT_LAYERS_NEXT = prove(`!l y. mld_ntt_layers (l + 1) y = mld_ntt_blocks l (2 EXP l) (mld_ntt_layers l y)`,
  REWRITE_TAC[GSYM ADD1; mld_ntt_layers]);;
let NTT_BLOCKS_NEXT = prove(`!l b r. mld_ntt_blocks l (b + 1) r =
   mld_ntt_block (mld_zeta (2 EXP l + b)) (2 * 2 EXP (7 - l) * b) (2 EXP (7 - l)) (mld_ntt_blocks l b r)`,
  REWRITE_TAC[GSYM ADD1; mld_ntt_blocks]);;
let NTT_LAYERS_EQ_INSTS =
  let red th = CONV_RULE(DEPTH_CONV NUM_RED_CONV) th in
  let ly l = red(SPECL [mk_small_numeral l; `y:num->int32`] NTT_LAYERS_NEXT) in
  let bl l b = red(SPECL [mk_small_numeral l; mk_small_numeral b; `r:num->int32`] NTT_BLOCKS_NEXT) in
  map ly (0--7) @
  [bl 0 0] @ map (bl 1) [0;1] @ map (bl 2) [0;1;2;3];;
let NTT_LAYERS_EQ =
  let m8 = `mld_ntt_blocks 7 128 (mld_ntt_blocks 6 64 (mld_ntt_blocks 5 32 (mld_ntt_blocks 4 16 (mld_ntt_blocks 3 8 (mld_ntt_block (mld_zeta 7) 192 32 (mld_ntt_block (mld_zeta 6) 128 32 (mld_ntt_block (mld_zeta 5) 64 32 (mld_ntt_block (mld_zeta 4) 0 32 (mld_ntt_block (mld_zeta 3) 128 64 (mld_ntt_block (mld_zeta 2) 0 64 (mld_ntt_block (mld_zeta 1) 0 128 (x:num->int32))))))))))))` in
  prove(mk_eq(`mld_ntt_layers 8 (x:num->int32)`, m8),
    REWRITE_TAC(NTT_LAYERS_EQ_INSTS @ [mld_ntt_layers; mld_ntt_blocks]) THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV));;


(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the 12 loops with   *)
(* the code between them, which loads the constants of the next loop and      *)
(* sets its registers, and the saving of RBX.                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  META_EXISTS_TAC THEN REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES; mld_poly_ntt; fst NTT_MAIN_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `nonoverlapping (a:int64,1024) (word(pc + rodata_mld_zetas),1024) /\
    nonoverlapping (a:int64,1024) (word(pc + mldsa_poly_ntt_consts),256) /\
    nonoverlapping (stackpointer:int64,8) (word(pc + rodata_mld_zetas),1024) /\
    nonoverlapping (stackpointer:int64,8) (word(pc + mldsa_poly_ntt_consts),256)`
  MP_TAC THENL [REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC; REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN STRIP_TAC] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  MAP_EVERY (fun k -> GHOST_INTRO_TAC (mk_var(Printf.sprintf "ymm%d_init" k, `:int256`)) (parse_term(Printf.sprintf "read YMM%d" k))) [0;1;2;3;4] THEN
  FULL_INIT_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLD_ZETAS_LOADED o MATCH_MP NTT_IMAGE_ZETAS o check (fun th -> can (term_match [] `bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc`) (concl th))) THEN
  X86_STEPS_TAC NTT_MAIN_EXEC (1--1) THEN
  X86_STEPS_TAC NTT_MAIN_EXEC (2--2) THEN
  NTT_CONST_STEP 0 0x13 3 THEN
  NTT_CONST_STEP 1 0x1b 4 THEN
  NTT_CONST_STEP 2 0x23 5 THEN
  NTT_CONST_STEP 3 0x2b 6 THEN
  X86_STEPS_TAC NTT_MAIN_EXEC (7--7) THEN
  MAP_EVERY NTT_XMM_OF_YMM_TAC [0;1;2] THEN
  MAP_EVERY NTT_XMM_OF_YMM_TAC [2;3;4] THEN
  NTT_ZREWRITE 1 true THEN
  EVENTS_BIGSTEP_TAC NTT_MAIN_EXEC (el 0 MLDSA_NTT_VEC_LOOPS) [`a:int64`; `pc:num`; `x:num->int32`; `mld_zeta 1`] 8 THEN
  X86_STEPS_TAC NTT_MAIN_EXEC (9--9) THEN
  X86_STEPS_TAC NTT_MAIN_EXEC (10--10) THEN
  NTT_CONST_STEP 4 0x178 11 THEN
  NTT_CONST_STEP 5 0x180 12 THEN
  MAP_EVERY NTT_XMM_OF_YMM_TAC [2;3;4] THEN
  NTT_ZREWRITE 2 false THEN
  EVENTS_BIGSTEP_TAC NTT_MAIN_EXEC (el 1 MLDSA_NTT_VEC_LOOPS) [`a:int64`; `pc:num`; `mld_ntt_block (mld_zeta 1) 0 128 (x)`; `mld_zeta 2`] 13 THEN
  X86_STEPS_TAC NTT_MAIN_EXEC (14--14) THEN
  X86_STEPS_TAC NTT_MAIN_EXEC (15--15) THEN
  NTT_CONST_STEP 6 0x2e6 16 THEN
  NTT_CONST_STEP 7 0x2ee 17 THEN
  X86_STEPS_TAC NTT_MAIN_EXEC (18--18) THEN
  MAP_EVERY NTT_XMM_OF_YMM_TAC [2;3;4] THEN
  NTT_ZREWRITE 3 false THEN
  EVENTS_BIGSTEP_TAC NTT_MAIN_EXEC (el 2 MLDSA_NTT_VEC_LOOPS) [`a:int64`; `pc:num`; `mld_ntt_block (mld_zeta 2) 0 64 (mld_ntt_block (mld_zeta 1) 0 128 (x:num->int32))`; `mld_zeta 3`] 19 THEN
  X86_STEPS_TAC NTT_MAIN_EXEC (20--20) THEN
  X86_STEPS_TAC NTT_MAIN_EXEC (21--21) THEN
  NTT_CONST_STEP 8 0x456 22 THEN
  NTT_CONST_STEP 9 0x45e 23 THEN
  X86_STEPS_TAC NTT_MAIN_EXEC (24--24) THEN
  MAP_EVERY NTT_XMM_OF_YMM_TAC [2;3;4] THEN
  NTT_ZREWRITE 4 true THEN
  EVENTS_BIGSTEP_TAC NTT_MAIN_EXEC (el 3 MLDSA_NTT_VEC_LOOPS) [`a:int64`; `pc:num`; `mld_ntt_block (mld_zeta 3) 128 64 (mld_ntt_block (mld_zeta 2) 0 64 (mld_ntt_block (mld_zeta 1) 0 128 (x:num->int32)))`; `mld_zeta 4`] 25 THEN
  X86_STEPS_TAC NTT_MAIN_EXEC (26--26) THEN
  X86_STEPS_TAC NTT_MAIN_EXEC (27--27) THEN
  NTT_CONST_STEP 10 0x5a8 28 THEN
  NTT_CONST_STEP 11 0x5b0 29 THEN
  MAP_EVERY NTT_XMM_OF_YMM_TAC [2;3;4] THEN
  NTT_ZREWRITE 5 false THEN
  EVENTS_BIGSTEP_TAC NTT_MAIN_EXEC (el 4 MLDSA_NTT_VEC_LOOPS) [`a:int64`; `pc:num`; `mld_ntt_block (mld_zeta 4) 0 32 (mld_ntt_block (mld_zeta 3) 128 64 (mld_ntt_block (mld_zeta 2) 0 64 (mld_ntt_block (mld_zeta 1) 0 128 (x:num->int32))))`; `mld_zeta 5`] 30 THEN
  X86_STEPS_TAC NTT_MAIN_EXEC (31--31) THEN
  X86_STEPS_TAC NTT_MAIN_EXEC (32--32) THEN
  NTT_CONST_STEP 12 0x716 33 THEN
  NTT_CONST_STEP 13 0x71e 34 THEN
  X86_STEPS_TAC NTT_MAIN_EXEC (35--35) THEN
  MAP_EVERY NTT_XMM_OF_YMM_TAC [2;3;4] THEN
  NTT_ZREWRITE 6 false THEN
  EVENTS_BIGSTEP_TAC NTT_MAIN_EXEC (el 5 MLDSA_NTT_VEC_LOOPS) [`a:int64`; `pc:num`; `mld_ntt_block (mld_zeta 5) 64 32 (mld_ntt_block (mld_zeta 4) 0 32 (mld_ntt_block (mld_zeta 3) 128 64 (mld_ntt_block (mld_zeta 2) 0 64 (mld_ntt_block (mld_zeta 1) 0 128 (x:num->int32)))))`; `mld_zeta 6`] 36 THEN
  X86_STEPS_TAC NTT_MAIN_EXEC (37--37) THEN
  X86_STEPS_TAC NTT_MAIN_EXEC (38--38) THEN
  NTT_CONST_STEP 14 0x886 39 THEN
  NTT_CONST_STEP 15 0x88e 40 THEN
  X86_STEPS_TAC NTT_MAIN_EXEC (41--41) THEN
  MAP_EVERY NTT_XMM_OF_YMM_TAC [2;3;4] THEN
  NTT_ZREWRITE 7 true THEN
  EVENTS_BIGSTEP_TAC NTT_MAIN_EXEC (el 6 MLDSA_NTT_VEC_LOOPS) [`a:int64`; `pc:num`; `mld_ntt_block (mld_zeta 6) 128 32 (mld_ntt_block (mld_zeta 5) 64 32 (mld_ntt_block (mld_zeta 4) 0 32 (mld_ntt_block (mld_zeta 3) 128 64 (mld_ntt_block (mld_zeta 2) 0 64 (mld_ntt_block (mld_zeta 1) 0 128 (x:num->int32))))))`; `mld_zeta 7`] 42 THEN
  X86_STEPS_TAC NTT_MAIN_EXEC (43--46) THEN
  X86_STEPS_TAC NTT_MAIN_EXEC (47--47) THEN
  NTT_RIPREL_RCX_TAC THEN
  X86_STEPS_TAC NTT_MAIN_EXEC (48--48) THEN
  EVENTS_BIGSTEP_TAC NTT_MAIN_EXEC MLDSA_NTT_L4_LOOP [`a:int64`; `pc:num`; `word(pc + 152736):int64`; `mld_ntt_block (mld_zeta 7) 192 32 (mld_ntt_block (mld_zeta 6) 128 32 (mld_ntt_block (mld_zeta 5) 64 32 (mld_ntt_block (mld_zeta 4) 0 32 (mld_ntt_block (mld_zeta 3) 128 64 (mld_ntt_block (mld_zeta 2) 0 64 (mld_ntt_block (mld_zeta 1) 0 128 (x:num->int32)))))))`] 49 THEN
  X86_STEPS_TAC NTT_MAIN_EXEC (50--52) THEN
  EVENTS_BIGSTEP_TAC NTT_MAIN_EXEC MLDSA_NTT_L5_LOOP [`a:int64`; `pc:num`; `word(pc + 152736):int64`; `mld_ntt_blocks 3 8 (mld_ntt_block (mld_zeta 7) 192 32 (mld_ntt_block (mld_zeta 6) 128 32 (mld_ntt_block (mld_zeta 5) 64 32 (mld_ntt_block (mld_zeta 4) 0 32 (mld_ntt_block (mld_zeta 3) 128 64 (mld_ntt_block (mld_zeta 2) 0 64 (mld_ntt_block (mld_zeta 1) 0 128 (x:num->int32))))))))`] 53 THEN
  X86_STEPS_TAC NTT_MAIN_EXEC (54--56) THEN
  EVENTS_BIGSTEP_TAC NTT_MAIN_EXEC MLDSA_NTT_L6_LOOP [`a:int64`; `pc:num`; `word(pc + 152736):int64`; `mld_ntt_blocks 4 16 (mld_ntt_blocks 3 8 (mld_ntt_block (mld_zeta 7) 192 32 (mld_ntt_block (mld_zeta 6) 128 32 (mld_ntt_block (mld_zeta 5) 64 32 (mld_ntt_block (mld_zeta 4) 0 32 (mld_ntt_block (mld_zeta 3) 128 64 (mld_ntt_block (mld_zeta 2) 0 64 (mld_ntt_block (mld_zeta 1) 0 128 (x:num->int32)))))))))`] 57 THEN
  X86_STEPS_TAC NTT_MAIN_EXEC (58--59) THEN
  EVENTS_BIGSTEP_TAC NTT_MAIN_EXEC MLDSA_NTT_L7_LOOP [`a:int64`; `pc:num`; `word(pc + 152736):int64`; `mld_ntt_blocks 5 32 (mld_ntt_blocks 4 16 (mld_ntt_blocks 3 8 (mld_ntt_block (mld_zeta 7) 192 32 (mld_ntt_block (mld_zeta 6) 128 32 (mld_ntt_block (mld_zeta 5) 64 32 (mld_ntt_block (mld_zeta 4) 0 32 (mld_ntt_block (mld_zeta 3) 128 64 (mld_ntt_block (mld_zeta 2) 0 64 (mld_ntt_block (mld_zeta 1) 0 128 (x:num->int32))))))))))`] 60 THEN
  X86_STEPS_TAC NTT_MAIN_EXEC (61--62) THEN
  EVENTS_BIGSTEP_TAC NTT_MAIN_EXEC MLDSA_NTT_L8_LOOP [`a:int64`; `pc:num`; `word(pc + 152736):int64`; `mld_ntt_blocks 6 64 (mld_ntt_blocks 5 32 (mld_ntt_blocks 4 16 (mld_ntt_blocks 3 8 (mld_ntt_block (mld_zeta 7) 192 32 (mld_ntt_block (mld_zeta 6) 128 32 (mld_ntt_block (mld_zeta 5) 64 32 (mld_ntt_block (mld_zeta 4) 0 32 (mld_ntt_block (mld_zeta 3) 128 64 (mld_ntt_block (mld_zeta 2) 0 64 (mld_ntt_block (mld_zeta 1) 0 128 (x:num->int32)))))))))))`] 63
  THEN
  X86_STEPS_TAC NTT_MAIN_EXEC (64--73) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[NTT_LAYERS_EQ] THEN ASM_REWRITE_TAC[] THEN
  EVENTS_APPEND_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;
