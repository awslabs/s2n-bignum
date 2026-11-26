(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The region lemmas of mld_H44 (and of mld_H65, whose code is the same at   *)
(* the same offsets from the function): the records of the XOR loops, of the *)
(* unrolled chunks and of the tail and fill regions for inline_hxor.ml, and  *)
(* of the block loops and the absorbs for inline_hphase.ml (offsets from the *)
(* function, see the listing in H_44_spec.ml). Nothing is proved at load     *)
(* time: H44_PROVE_ALL fn proves the region lemmas for fn = "mld_H44" or     *)
(* "mld_H65", and H44_TOP_TAC composes them into the proof of the function.  *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_hphase.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_hsqueeze.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_h.ml";;

let hx44 h e k d b s i c cnt kp = { hx_fn = "mld_H44"; hx_head = h; hx_exit = e; hx_kind = k;
   hx_dst = d; hx_bias = b; hx_src = s; hx_idx = i; hx_ctl = c; hx_count = cnt; hx_keep = kp };;
let KC0 = ["RAX","word c0"] and KLEN = ["RAX","word len"];;
let H44_L4  = hx44 0x1f0 0x217 "va" "RSP" 16 "RBP" "RCX" "RAX" false [];;
let H44_L5  = hx44 0x240 0x251 "d"  "RSP" 16 "RBP" "RCX" "RAX" false [];;
let H44_L2  = hx44 0x180 0x192 "b"  "RSP" 16 "RBP" "RCX" "RDX" true KC0;;
let H44_L6  = hx44 0x470 0x481 "d"  "RCX" 0 "R13" "RSI" "RDX" false KLEN;;
let H44_J13 = hx44 0x490 0x4a2 "b"  "RCX" 0 "R13" "RDX" "RAX" false [];;
let H44_L15 = hx44 0x930 0x95f "vu" "RBP" 0 "R13" "RCX" "RAX" false [];;
let H44_L16 = hx44 0x980 0x992 "d"  "RBP" 0 "R13" "RCX" "RAX" false [];;
let H44_L7  = hx44 0x4f0 0x503 "b"  "RBP" 0 "R13" "RCX" "RDX" true KC0;;
let H44_L9  = hx44 0x600 0x62d "vu" "RSI" 16 "R13" "RDI" "RDX" false (KLEN @ ["RCX","word_add a (word off)"]);;
let H44_L10 = hx44 0x650 0x661 "d"  "RCX" 0 "R13" "RSI" "RDX" false KLEN;;
let H44_J26 = hx44 0x670 0x682 "b"  "RCX" 0 "R13" "RDX" "RAX" false [];;
let H44_L13 = hx44 0x8b0 0x8e1 "vu" "R12" 0 "R13" "RCX" "RAX" false [];;
let H44_L14 = hx44 0x900 0x912 "d"  "R12" 0 "R13" "RCX" "RAX" false [];;
let H44_L11 = hx44 0x6d0 0x6e2 "b"  "R12" 0 "R13" "RCX" "RDX" true KC0;;
let H44_T2 = { rg_fn = "mld_H44"; rg_entry = 0x4b3; rg_exit = 0x541; rg_dst = "RBP"; rg_bias = 0;
               rg_src = "R13"; rg_len = "R12"; rg_v32 = H44_L15; rg_v4 = H44_L16; rg_v1 = H44_L7 };;
let H44_U2 = { (HXU_CHUNK_LOOP "mld_H44") with hx_head = 0x2f0; hx_exit = 0x450 };;
let H44_F2 = { rg_fn = "mld_H44"; rg_entry = 0x2ce; rg_exit = 0x2a0; rg_dst = "RCX"; rg_bias = 0;
               rg_src = "R13"; rg_len = "RAX"; rg_v32 = H44_U2; rg_v4 = H44_L6; rg_v1 = H44_J13 };;

let H44_B2 = { bk_fn = "mld_H44"; bk_head = 0x2c6; bk_fill = 0x2ce; bk_exit = 0x4a7; bk_so = 16; bk_fr = 528;
               bk_len = "R12"; bk_dat = "R13"; bk_st = "RBP"; bk_keep = []; bk_call = 0x2a9 };;

let H44_P2 = { ph_fn = "mld_H44"; ph_entry = 0x25a; ph_exit = 0x551; ph_so = 16; ph_fr = 528;
  ph_len = "R12"; ph_dat = "R13";
  ph_pre = "read R12 s = word len /\\ read R13 s = m /\\ read (memory :> bytes64 (word_add bq (word 304))) s = out /\\ read (memory :> bytes64 (word_add bq (word 592))) s = word x /\\";
  ph_post = "read R14 s = word x /\\ read RBP s = out /\\";
  ph_mc = "RBP; R12; R13; R14; R15";
  ph_args = "word_add bq (word 304),8; word_add bq (word 592),8;";
  ph_tail = 0x4b3; ph_tdst = "RBP"; ph_blk = 0x2c6 };;

(* the third absorb: the JAE overlap test, the tail, the fill (with a       *)
(* 32-byte loop through RSI = state + off + 16, RBP = state + 16), the      *)
(* block loop and the whole absorb (in3 from its slot at bq + 584)          *)
let H44_A3 = ("mld_H44",0x69e,0x88c,"R12","R13","R14");;
let H44_T3 = { rg_fn = "mld_H44"; rg_entry = 0x698; rg_exit = 0x724; rg_dst = "R12"; rg_bias = 0;
               rg_src = "R13"; rg_len = "R14"; rg_v32 = H44_L13; rg_v4 = H44_L14; rg_v1 = H44_L11 };;
let H44_F3 = { rg_fn = "mld_H44"; rg_entry = 0x5c7; rg_exit = 0x590; rg_dst = "RCX"; rg_bias = 0;
               rg_src = "R13"; rg_len = "RAX"; rg_v32 = H44_L9; rg_v4 = H44_L10; rg_v1 = H44_J26 };;
let H44_F3_XPRE = "read RSI s = word off /\\ read RBP s = word_add a (word 16) /\\";;
let H44_B3 = { bk_fn = "mld_H44"; bk_head = 0x5b3; bk_fill = 0x5c7; bk_exit = 0x687; bk_so = 16; bk_fr = 528;
               bk_len = "R14"; bk_dat = "R13"; bk_st = "R12"; bk_keep = ["RBP","word_add bq (word 328)"];
               bk_call = 0x599 };;
let H44_P3 = { ph_fn = "mld_H44"; ph_entry = 0x551; ph_exit = 0x72f; ph_so = 16; ph_fr = 528;
  ph_len = "R14"; ph_dat = "R13";
  ph_pre = "read R14 s = word len /\\ read (memory :> bytes64 (word_add bq (word 584))) s = m /\\ read RBP s = out /\\ read (memory :> bytes64 (word_add bq (word 304))) s = out /\\";
  ph_post = "read RBP s = out /\\";
  ph_mc = "RBP; R12; R13; R14; R15";
  ph_args = "word_add bq (word 304),8; word_add bq (word 584),8;";
  ph_tail = 0x698; ph_tdst = "R12"; ph_blk = 0x5b3 };;

(* the first absorb: the SETB overlap test of the tail, the tail (state at  *)
(* rsp0 + 16, data RBP, length R15), and the whole absorb (zeroing, loop1)  *)
let H44_A1 = ("mld_H44",0x147,0x1d2,16,"RBP","R15",10);;
let H44_T1 = { rg_fn = "mld_H44"; rg_entry = 0x141; rg_exit = 0x25a; rg_dst = "RSP"; rg_bias = 16;
               rg_src = "RBP"; rg_len = "R15"; rg_v32 = H44_L4; rg_v4 = H44_L5; rg_v1 = H44_L2 };;
let H44_P1 = { p1_fn = "mld_H44"; p1_entry = 0x25; p1_zend = 0x7b; p1_loop = 0x90; p1_tail = 0x141;
               p1_exit = 0x25a; p1_so = 16; p1_fr = 528; p1_dat = "RBP"; p1_len = "R15"; p1_st = "R14";
               p1_mc = "RBP; R14; R15"; p1_cmp = "RCX" };;

(* ------------------------------------------------------------------------- *)
(* All region lemmas of mld_H44, or of mld_H65 (the same code): the records  *)
(* above with the function name fn, proved in the order of their use.        *)
(* ------------------------------------------------------------------------- *)

let hx_at fn (l:hx_loop) = { l with hx_fn = fn };;
let rg_at fn (g:hx_region) =
  { g with rg_fn = fn; rg_v32 = hx_at fn g.rg_v32; rg_v4 = hx_at fn g.rg_v4; rg_v1 = hx_at fn g.rg_v1 };;

type h44_lemmas = { hp1 : thm; hp2 : thm; hp3 : thm; hsq : thm };;

let H_TIMED name f =
  let t0 = Unix.gettimeofday() in
  let th = f () in
  Printf.printf "H_TIME %s %.1f\n%!" name (Unix.gettimeofday() -. t0); th;;

let H44_PROVE_ALL fn =
  let tm n f = H_TIMED (fn ^ " " ^ n) f in
  let loop n l = tm n (fun () -> HX_PROVE (hx_at fn l)) in
  (* the first absorb: zeroing, loop1, the tail with the SETB overlap test *)
  let z = tm "Z" (fun () -> HX_ZERO_PROVE fn 16 0x25 0x7b) in
  let l1 = tm "L1" (fun () -> PROVE_SPONGE_L1G fn "RBP" "R15" "R14" 16) in
  let a1 = tm "A1" (fun () -> let (_,e0,e1,so,m,l,n) = H44_A1 in HXA1_PROVE fn e0 e1 so m l n) in
  let tl4 = loop "L4" H44_L4 and tl5 = loop "L5" H44_L5 and tl2 = loop "L2" H44_L2 in
  let g1 = rg_at fn H44_T1 in
  let t1 = tm "T1" (fun () -> prove(HXR_STMT true g1, HXR_TAIL_ALIAS_TAC 0x147 a1 g1 tl4 tl5 tl2)) in
  let q1 = { H44_P1 with p1_fn = fn } in
  let p1 = tm "P1" (fun () -> prove(HXP1_STMT q1, HXP1_TAC q1 z l1 t1)) in
  (* the second absorb: tail, fill (unrolled chunks), block loop *)
  let tl15 = loop "L15" H44_L15 and tl16 = loop "L16" H44_L16 and tl7 = loop "L7" H44_L7 in
  let g2 = rg_at fn H44_T2 in
  let t2 = tm "T2" (fun () -> prove(HXR_STMT true g2, HXR_TAIL_TAC [] g2 tl15 tl16 tl7)) in
  let u2 = tm "U2" (fun () -> HXU_PROVE fn 0x2f0 0x450) in
  let tl6 = loop "L6" H44_L6 and tj13 = loop "J13" H44_J13 in
  let f2r = rg_at fn H44_F2 in
  let f2 = tm "F2" (fun () -> prove(HXR_STMT false f2r, HXR_FILL_TAC f2r u2 tl6 tj13)) in
  let b2 = tm "B2" (fun () -> HXB_PROVE { H44_B2 with bk_fn = fn } f2 [] 4) in
  let q2 = { H44_P2 with ph_fn = fn } in
  let p2 = tm "P2" (fun () -> prove(HXP_STMT q2, HXP_TAC q2 t2 b2)) in
  (* the third absorb: the JAE overlap test, tail, fill (32-byte loop), block loop *)
  let a3 = tm "A3" (fun () -> let (_,e0,e1,d,m,l) = H44_A3 in HXA_PROVE fn e0 e1 d m l) in
  let tl13 = loop "L13" H44_L13 and tl14 = loop "L14" H44_L14 and tl11 = loop "L11" H44_L11 in
  let g3 = rg_at fn H44_T3 in
  let t3 = tm "T3" (fun () -> prove(HXR_STMT true g3, HXR_TAIL_ALIAS_TAC 0x69e a3 g3 tl13 tl14 tl11)) in
  let tl9 = loop "L9" H44_L9 and tl10 = loop "L10" H44_L10 and tj26 = loop "J26" H44_J26 in
  let f3r = rg_at fn H44_F3 in
  let f3 = tm "F3" (fun () -> prove(HXR_STMT_X false f3r H44_F3_XPRE, HXR_FILLV_TAC "RSI" f3r tl9 tl10 tj26)) in
  let b3 = tm "B3" (fun () -> HXB_PROVE { H44_B3 with bk_fn = fn } f3 (hx_p32 `pp:num`) 4) in
  let q3 = { H44_P3 with ph_fn = fn } in
  let p3 = tm "P3" (fun () -> prove(HXP_STMT q3, HXP_TAC q3 t3 b3)) in
  (* the padding and the squeeze *)
  let sq = tm "SQ" (fun () -> HXS_PROVE { H44_SQ with sq_fn = fn }) in
  { hp1 = p1; hp2 = p2; hp3 = p3; hsq = sq };;

(* ------------------------------------------------------------------------- *)
(* The top level of mld_H44 and mld_H65, composed of the region lemmas as    *)
(* the gcc proof composes the calls of the shake256 functions. After the     *)
(* offset of the stack pointer, the frame is stackpointer .. + 576: the      *)
(* callees' stack the first 296 bytes, then the slot of out (+ 304), the     *)
(* state (+ 312) and its position (+ 512), the saved registers (+ 528) and   *)
(* the return address; in3 and in3len are at + 584 and + 592. The absorbs    *)
(* append their inputs (MLD_SHAKE256_ABSORB_APPEND/APPEND3); the squeeze      *)
(* leaves the output; then the code zeroes the state with 26 MOVAPS stores   *)
(* (aligned, since stackpointer + 584 is) and returns.                       *)
(* ------------------------------------------------------------------------- *)

(* the pieces shared with mld_H87: the alignment of the state (at            *)
(* stackpointer + 296) from that of stackpointer + off (the ABI alignment of *)
(* the caller), the bounds of the inputs and positions, the alignment facts  *)
(* of the zeroing stores at the state + 16 j, and the end                    *)
let H_ALIGN_TAC off =
  let d = mk_small_numeral (off - 296) and ov = mk_small_numeral off in
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 296):int64)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`16`; `word_add stackpointer (word 296):int64`; mk_comb(`word:num->int64`,d)]
                  (CONJUNCT2 ALIGNED_WORD_ADD_EQ)) THEN
    REWRITE_TAC[SPONGE_A16 (off - 296);
                WORD_RULE (subst [d,`d:num`; ov,`n:num`]
                  `word_add (word_add (x:int64) (word 296)) (word d) = word_add x (word n)`)] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]; ALL_TAC];;

let H_BOUNDS_TAC =
  SUBGOAL_THEN `M1 < 2 EXP (8 * in1len) /\ M2 < 2 EXP (8 * in2len) /\ M3 < 2 EXP (8 * in3len)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes (m,l)) s0 = x`) (concl th) &&
                             is_var(rhs(concl th)) && mem (fst(dest_var(rhs(concl th)))) ["M1";"M2";"M3"] then
      (W(fun (_,w) -> if rhs(concl th) = lhand w then
         SUBST1_TAC(SYM th) THEN REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND] else NO_TAC))
      else NO_TAC); ALL_TAC] THEN
  SUBGOAL_THEN `in1len MOD 136 < 136 /\ (in1len + in2len) MOD 136 < 136 /\ (in1len + in2len + in3len) MOD 136 < 136`
    STRIP_ASSUME_TAC THENL [REWRITE_TAC[MOD_LT_EQ; ARITH_EQ]; ALL_TAC];;

(* after the absorb of in2 and of in3: the state and position as those of    *)
(* the absorb of the concatenation                                           *)
let H_APPEND2_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPECL [`in1len:num`; `in2len:num`; `M1:num`; `M2:num`] MLD_SHAKE256_ABSORB_APPEND) (ASSUME `M1 < 2 EXP (8 * in1len)`)]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_KECCAK_ABSORB_SND; ADD_CLAUSES]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_KECCAK_POS_ADD]);;

let H_APPEND3_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPECL [`in1len:num`; `in2len:num`; `in3len:num`; `M1:num`; `M2:num`; `M3:num`] MLD_SHAKE256_ABSORB_APPEND3)
       (CONJ (ASSUME `M1 < 2 EXP (8 * in1len)`) (ASSUME `M2 < 2 EXP (8 * in2len)`))]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_KECCAK_ABSORB_SND; MLD_KECCAK_POS_ADD; GSYM ADD_ASSOC; ADD_CLAUSES]);;

let H_ZERO_ALIGN_TAC js =
  W(fun (asl,w) -> YMM_GHOST_TAC (hx_cur_state asl) ["YMM0","y0"]) THEN
  FIRST_ASSUM(fun ra -> if concl ra = `aligned 16 (word_add stackpointer (word 296):int64)` then
    MAP_EVERY (fun k -> let th = MATCH_MP ALIGNED_WORD_ADD (CONJ ra (SPONGE_A16 k)) in
       ASSUME_TAC th THEN
       ASSUME_TAC (CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC DEPTH_CONV NUM_ADD_CONV) th))
     (map (fun j -> 16 * j) js) else NO_TAC);;

let H_STEPS_TAC exec n = W(fun (asl,w) -> let k = hx_state_num asl in X86_STEPS_TAC exec ((k+1)--(k+n)));;

let H_FINAL_TAC =
  REWRITE_TAC[mld_shake256_byte; mld_shake256_state; MLD_KECCAK_ABSORB_SND; ADD_CLAUSES] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MLD_H_DISCHARGE_TAC;;

let H44_TOP_VARS =
  [`out:int64`; `outlen:num`; `in1:int64`; `in1len:num`; `in2:int64`; `in2len:num`;
   `in3:int64`; `in3len:num`; `mc:int64`; `pc:num`; `stackpointer:int64`; `returnaddress:int64`];;

let H44_TOP_TAC exec lem =
  let call name ilist = HX_LCALL_TAC exec name ilist H44_TOP_VARS in
  REPEAT GEN_TAC THEN DISCH_THEN(fun mcp ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
      (SPONGE_RENAME_E2 (MP (SPECL [`mc:int64`;`ea:int64`;`el:num`;`ev:num`] lem.hsq) mcp)) "H_SQ") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 lem.hp1) "H_P1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 lem.hp2) "H_P2" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 lem.hp3) "H_P3" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(out:int64) (outlen:num) (in1:int64) (in1len:num) (in2:int64) (in2len:num) (in3:int64) (in3len:num)
     (mc:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      f_ev_all out outlen in1 in1len in2 in2len in3 in3len mc pc stackpointer returnaddress :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE;
              NONOVERLAPPING_CLAUSES; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN ENSURES_PRESERVED_TAC "r15_init" `R15` THEN
  FULL_INIT_TAC THEN
  (* the prologue: 6 pushes, the frame, the arguments in registers *)
  X86_STEPS_TAC exec (1--13) THEN
  HX_NOV_SHRINK_TAC 576 528 THEN H_ALIGN_TAC 584 THEN
  (* the three absorbs *)
  call "H_P1" [`stackpointer:int64`; `in1:int64`; `in1len:num`; `M1:num`; `pc:num`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_KECCAK_ABSORB_SND; ADD_CLAUSES]) THEN
  H_BOUNDS_TAC THEN
  call "H_P2" [`stackpointer:int64`; `in1len MOD 136`; `in2:int64`; `in2len:num`; `M2:num`;
               `FST(mld_keccak_absorb 136 (word 0) 0 in1len M1)`; `out:int64`; `in3len:num`; `pc:num`] THEN
  H_APPEND2_TAC THEN
  call "H_P3" [`stackpointer:int64`; `(in1len + in2len) MOD 136`; `in3:int64`; `in3len:num`; `M3:num`;
               `FST(mld_keccak_absorb 136 (word 0) 0 (in1len + in2len) (M1 + 2 EXP (8 * in1len) * M2))`;
               `out:int64`; `pc:num`] THEN
  H_APPEND3_TAC THEN
  (* the padding and the squeeze *)
  call "H_SQ" [`stackpointer:int64`; `(in1len + in2len + in3len) MOD 136`;
               `FST(mld_keccak_absorb 136 (word 0) 0 (in1len + in2len + in3len)
                      (M1 + 2 EXP (8 * in1len) * (M2 + 2 EXP (8 * in2len) * M3)))`;
               `out:int64`; `outlen:num`; `pc:num`] THEN
  (* the zeroing of the state: xorps, 26 movaps at rsp + 16 j, and the epilogue *)
  H_ZERO_ALIGN_TAC (1--13) THEN H_STEPS_TAC exec 28 THEN
  H_STEPS_TAC exec 15 THEN
  H_FINAL_TAC;;
