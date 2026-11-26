(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The region lemmas of mld_H87: the records of H_44_inline.ml for the code  *)
(* of mld_H87, which has the shape of mld_H44 with the state at the stack    *)
(* pointer (offset 0 instead of 16), other registers (in2 R13/R12 as in      *)
(* mld_H44, in3 R14 with its length in RBX) and other offsets (see the       *)
(* listing in H_87_spec.ml). The frame of the region lemmas is the 512 bytes *)
(* below the saved registers.                                                *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/H_44_inline.ml";;

let hx87 h e k d b s i c cnt kp = { hx_fn = "mld_H87"; hx_head = h; hx_exit = e; hx_kind = k;
   hx_dst = d; hx_bias = b; hx_src = s; hx_idx = i; hx_ctl = c; hx_count = cnt; hx_keep = kp };;

(* the first absorb: tail at the state (RSP), data RBP, length R15           *)
let H87_L4  = hx87 0x1e0 0x205 "va" "RSP" 0 "RBP" "RCX" "RAX" false [];;
let H87_L5  = hx87 0x220 0x230 "d"  "RSP" 0 "RBP" "RCX" "RAX" false [];;
let H87_L2  = hx87 0x170 0x181 "b"  "RSP" 0 "RBP" "RCX" "RDX" true KC0;;
let H87_A1 = ("mld_H87",0x13f,0x1be,0,"RBP","R15",9);;
let H87_T1 = { rg_fn = "mld_H87"; rg_entry = 0x139; rg_exit = 0x239; rg_dst = "RSP"; rg_bias = 0;
               rg_src = "RBP"; rg_len = "R15"; rg_v32 = H87_L4; rg_v4 = H87_L5; rg_v1 = H87_L2 };;
let H87_P1 = { p1_fn = "mld_H87"; p1_entry = 0x28; p1_zend = 0x7a; p1_loop = 0x90; p1_tail = 0x139;
               p1_exit = 0x239; p1_so = 0; p1_fr = 512; p1_dat = "RBP"; p1_len = "R15"; p1_st = "RBX";
               p1_mc = "RBP; RBX; R15"; p1_cmp = "RDX" };;

(* the second absorb: data R13, length R12, tail at RBP, fill at RCX         *)
let H87_L15 = hx87 0x890 0x8bf "vu" "RBP" 0 "R13" "RCX" "RAX" false [];;
let H87_L16 = hx87 0x8e0 0x8f2 "d"  "RBP" 0 "R13" "RCX" "RAX" false [];;
let H87_L7  = hx87 0x4c0 0x4d3 "b"  "RBP" 0 "R13" "RCX" "RDX" true KC0;;
let H87_L6  = hx87 0x440 0x451 "d"  "RCX" 0 "R13" "RSI" "RDX" false KLEN;;
let H87_J13 = hx87 0x460 0x472 "b"  "RCX" 0 "R13" "RDX" "RAX" false [];;
let H87_T2 = { rg_fn = "mld_H87"; rg_entry = 0x483; rg_exit = 0x511; rg_dst = "RBP"; rg_bias = 0;
               rg_src = "R13"; rg_len = "R12"; rg_v32 = H87_L15; rg_v4 = H87_L16; rg_v1 = H87_L7 };;
let H87_U2 = { (HXU_CHUNK_LOOP "mld_H87") with hx_head = 0x2c0; hx_exit = 0x420 };;
let H87_F2 = { rg_fn = "mld_H87"; rg_entry = 0x29a; rg_exit = 0x270; rg_dst = "RCX"; rg_bias = 0;
               rg_src = "R13"; rg_len = "RAX"; rg_v32 = H87_U2; rg_v4 = H87_L6; rg_v1 = H87_J13 };;
let H87_B2 = { bk_fn = "mld_H87"; bk_head = 0x296; bk_fill = 0x29a; bk_exit = 0x477; bk_so = 0; bk_fr = 512;
               bk_len = "R12"; bk_dat = "R13"; bk_st = "RBP"; bk_keep = []; bk_call = 0x279 };;
let H87_P2 = { ph_fn = "mld_H87"; ph_entry = 0x239; ph_exit = 0x51c; ph_so = 0; ph_fr = 512;
  ph_len = "R12"; ph_dat = "R13";
  ph_pre = "read R12 s = word len /\\ read R13 s = m /\\ read (memory :> bytes64 (word_add bq (word 568))) s = word x /\\";
  ph_post = "read RBX s = word x /\\";
  ph_mc = "RBX; RBP; R12; R13; R15";
  ph_args = "word_add bq (word 568),8;";
  ph_tail = 0x483; ph_tdst = "RBP"; ph_blk = 0x296 };;

(* the third absorb: data R14, length RBX, tail and block state at R12       *)
let H87_L13 = hx87 0x810 0x840 "vu" "R12" 0 "R14" "RCX" "RAX" false [];;
let H87_L14 = hx87 0x860 0x871 "d"  "R12" 0 "R14" "RCX" "RAX" false [];;
let H87_L11 = hx87 0x680 0x691 "b"  "R12" 0 "R14" "RCX" "RDX" true KC0;;
let H87_L9  = hx87 0x5b0 0x5dc "vu" "RSI" 16 "R14" "RDI" "RDX" false (KLEN @ ["RCX","word_add a (word off)"]);;
let H87_L10 = hx87 0x600 0x610 "d"  "RCX" 0 "R14" "RSI" "RDX" false KLEN;;
let H87_J26 = hx87 0x620 0x631 "b"  "RCX" 0 "R14" "RDX" "RAX" false [];;
let H87_A3 = ("mld_H87",0x648,0x7f0,"R12","R14","RBX");;
let H87_T3 = { rg_fn = "mld_H87"; rg_entry = 0x642; rg_exit = 0x6d3; rg_dst = "R12"; rg_bias = 0;
               rg_src = "R14"; rg_len = "RBX"; rg_v32 = H87_L13; rg_v4 = H87_L14; rg_v1 = H87_L11 };;
let H87_F3 = { rg_fn = "mld_H87"; rg_entry = 0x583; rg_exit = 0x550; rg_dst = "RCX"; rg_bias = 0;
               rg_src = "R14"; rg_len = "RAX"; rg_v32 = H87_L9; rg_v4 = H87_L10; rg_v1 = H87_J26 };;
let H87_F3_XPRE = "read RSI s = word off /\\ read R13 s = word_add a (word 16) /\\";;
let H87_B3 = { bk_fn = "mld_H87"; bk_head = 0x573; bk_fill = 0x583; bk_exit = 0x636; bk_so = 0; bk_fr = 512;
               bk_len = "RBX"; bk_dat = "R14"; bk_st = "R12"; bk_keep = ["R13","word_add bq (word 312)"];
               bk_call = 0x559 };;
let H87_P3 = { ph_fn = "mld_H87"; ph_entry = 0x51c; ph_exit = 0x6de; ph_so = 0; ph_fr = 512;
  ph_len = "RBX"; ph_dat = "R14";
  ph_pre = "read RBX s = word len /\\ read R14 s = m /\\";
  ph_post = "";
  ph_mc = "RBX; R12; R13; R14; R15";
  ph_args = "";
  ph_tail = 0x642; ph_tdst = "R12"; ph_blk = 0x573 };;

(* the padding, one permutation and the copy of 64 bytes to out (in the      *)
(* stack slot at bq + 504)                                                   *)
let H87_SQ = { s6_fn = "mld_H87"; s6_entry = 0x6de; s6_exit = 0x72d; s6_so = 0; s6_fr = 512; s6_out = 504 };;

(* ------------------------------------------------------------------------- *)
(* All region lemmas of mld_H87, in the order of their use.                  *)
(* ------------------------------------------------------------------------- *)

let H87_PROVE_ALL () =
  let fn = "mld_H87" in
  let tm n f = H_TIMED (fn ^ " " ^ n) f in
  let loop n l = tm n (fun () -> HX_PROVE l) in
  (* the first absorb: zeroing, loop1, the tail with the SETB overlap test *)
  let z = tm "Z" (fun () -> HX_ZERO_PROVE fn 0 0x28 0x7a) in
  let l1 = tm "L1" (fun () -> PROVE_SPONGE_L1G fn "RBP" "R15" "RBX" 0) in
  let a1 = tm "A1" (fun () -> let (_,e0,e1,so,m,l,n) = H87_A1 in HXA1_PROVE fn e0 e1 so m l n) in
  let tl4 = loop "L4" H87_L4 and tl5 = loop "L5" H87_L5 and tl2 = loop "L2" H87_L2 in
  let t1 = tm "T1" (fun () -> prove(HXR_STMT true H87_T1, HXR_TAIL_ALIAS_TAC 0x13f a1 H87_T1 tl4 tl5 tl2)) in
  let p1 = tm "P1" (fun () -> prove(HXP1_STMT H87_P1, HXP1_TAC H87_P1 z l1 t1)) in
  (* the second absorb: tail, fill (unrolled chunks), block loop *)
  let tl15 = loop "L15" H87_L15 and tl16 = loop "L16" H87_L16 and tl7 = loop "L7" H87_L7 in
  let t2 = tm "T2" (fun () -> prove(HXR_STMT true H87_T2, HXR_TAIL_TAC [] H87_T2 tl15 tl16 tl7)) in
  let u2 = tm "U2" (fun () -> HXU_PROVE fn 0x2c0 0x420) in
  let tl6 = loop "L6" H87_L6 and tj13 = loop "J13" H87_J13 in
  let f2 = tm "F2" (fun () -> prove(HXR_STMT false H87_F2, HXR_FILL_TAC H87_F2 u2 tl6 tj13)) in
  let b2 = tm "B2" (fun () -> HXB_PROVE H87_B2 f2 [] 4) in
  let p2 = tm "P2" (fun () -> prove(HXP_STMT H87_P2, HXP_TAC H87_P2 t2 b2)) in
  (* the third absorb: the JAE overlap test (end of the data as m + r), tail, fill, block loop *)
  let a3 = tm "A3" (fun () -> let (_,e0,e1,d,m,l) = H87_A3 in HXA_PROVE_G fn e0 e1 d m l true) in
  let tl13 = loop "L13" H87_L13 and tl14 = loop "L14" H87_L14 and tl11 = loop "L11" H87_L11 in
  let t3 = tm "T3" (fun () -> prove(HXR_STMT true H87_T3, HXR_TAIL_ALIAS_TAC 0x648 a3 H87_T3 tl13 tl14 tl11)) in
  let tl9 = loop "L9" H87_L9 and tl10 = loop "L10" H87_L10 and tj26 = loop "J26" H87_J26 in
  let f3 = tm "F3" (fun () -> prove(HXR_STMT_X false H87_F3 H87_F3_XPRE, HXR_FILLV_TAC "RSI" H87_F3 tl9 tl10 tj26)) in
  let b3 = tm "B3" (fun () -> HXB_PROVE H87_B3 f3 (hx_p32 `pp:num`) 4) in
  let p3 = tm "P3" (fun () -> prove(HXP_STMT H87_P3, HXP_TAC H87_P3 t3 b3)) in
  (* the padding, the permutation and the copy of 64 bytes *)
  let sq = tm "SQ" (fun () -> HXS64_PROVE H87_SQ) in
  { hp1 = p1; hp2 = p2; hp3 = p3; hsq = sq };;

(* ------------------------------------------------------------------------- *)
(* The top level of mld_H87. After the offset of the stack pointer, the      *)
(* frame is stackpointer .. + 560: the callees' stack the first 296 bytes,   *)
(* the state (+ 296) and its position (+ 496), the slot of out (+ 504), the  *)
(* saved registers (+ 512) and the return address; in3len is at + 568. The   *)
(* squeeze lemma ends before the zeroing of the state (xorps and 26 MOVAPS). *)
(* ------------------------------------------------------------------------- *)

let H87_TOP_VARS =
  [`out:int64`; `in1:int64`; `in1len:num`; `in2:int64`; `in2len:num`;
   `in3:int64`; `in3len:num`; `mc:int64`; `pc:num`; `stackpointer:int64`; `returnaddress:int64`];;

let H87_TOP_TAC exec lem =
  let call name ilist = HX_LCALL_TAC exec name ilist H87_TOP_VARS in
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 lem.hsq) "H_SQ" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 lem.hp1) "H_P1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 lem.hp2) "H_P2" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 lem.hp3) "H_P3" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(out:int64) (in1:int64) (in1len:num) (in2:int64) (in2len:num) (in3:int64) (in3len:num)
     (mc:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      f_ev_all out in1 in1len in2 in2len in3 in3len mc pc stackpointer returnaddress :(uarch_event)list` THEN
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
  HX_NOV_SHRINK_TAC 560 512 THEN H_ALIGN_TAC 568 THEN
  (* the three absorbs; out and x are not in the lemmas of mld_H87 where they are unused *)
  call "H_P1" [`stackpointer:int64`; `in1:int64`; `in1len:num`; `M1:num`; `pc:num`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_KECCAK_ABSORB_SND; ADD_CLAUSES]) THEN
  H_BOUNDS_TAC THEN
  call "H_P2" [`stackpointer:int64`; `in1len MOD 136`; `in2:int64`; `in2len:num`; `M2:num`;
               `FST(mld_keccak_absorb 136 (word 0) 0 in1len M1)`; `in3len:num`; `pc:num`] THEN
  H_APPEND2_TAC THEN
  call "H_P3" [`stackpointer:int64`; `(in1len + in2len) MOD 136`; `in3:int64`; `in3len:num`; `M3:num`;
               `FST(mld_keccak_absorb 136 (word 0) 0 (in1len + in2len) (M1 + 2 EXP (8 * in1len) * M2))`;
               `pc:num`] THEN
  H_APPEND3_TAC THEN
  (* the padding, the permutation and the output *)
  call "H_SQ" [`stackpointer:int64`; `(in1len + in2len + in3len) MOD 136`;
               `FST(mld_keccak_absorb 136 (word 0) 0 (in1len + in2len + in3len)
                      (M1 + 2 EXP (8 * in1len) * (M2 + 2 EXP (8 * in2len) * M3)))`;
               `out:int64`; `pc:num`] THEN
  (* the zeroing of the state: xorps, 26 movaps at rsp + 16 j, and the epilogue *)
  H_ZERO_ALIGN_TAC (1--12) THEN H_STEPS_TAC exec 27 THEN
  H_STEPS_TAC exec 15 THEN
  H_FINAL_TAC;;
