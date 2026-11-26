(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* PACK4: mld_polyeta_pack for eta = 4 (ML-DSA-65) as clang 23 -O3 inlines   *)
(* it into mldsa65_keypair_internal of the monolithic reduced-RAM build, as  *)
(* a lemma from the head of the loop to its exit (see inline_sign.ml for the *)
(* form of the lemmas). The loop is vectorised with SSE2: each of its 16     *)
(* iterations loads 16 coefficients of the polynomial at rsp0 + cb with four *)
(* aligned MOVDQA from [rsp + rax * 8 + dl + 16 q], RAX = a0 + 8 i, packs    *)
(* 4 - a into a nibble per coefficient with PAND, PACKUSWB, PSHUFD, PSHUFLW, *)
(* PSUBB and POR, and stores the 8 bytes with two MOVD to [rbx + rax + ds]   *)
(* and [rbx + rax + ds + 4], that is rb + ob + 8 i with ob = ds + a0, for    *)
(* cb = dl + 8 a0. The six vectors of constants (the masks of the lanes and  *)
(* the bytes 4 and 0x40 to subtract from) are in XMM8 to XMM13, which the    *)
(* code loads from mldsa65_keypair_internal_const1..6 before the first loop  *)
(* of each group. The instances differ in a0, dl (which may be negative) and *)
(* ds; their bodies are the same 55 instructions.                            *)
(*                                                                           *)
(* The PAND with a mask of one byte per lane before each PACKUSWB makes the  *)
(* packed values fit a byte, so that the saturation of PACKUSWB never        *)
(* applies, and the bytes stored are mld_polyeta_pack_4 by bit-blasting, the *)
(* coefficients being atoms.                                                 *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_keypair.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_rl.ml";;

let KPPACK4_CONSTS =
  ["XMM8", "0x00000000000000ff00000000000000ff";
   "XMM9", "0x04040404";
   "XMM10", "0x00ff00ff00ff00ff00ff00ff00ff00ff";
   "XMM11", "0xffffffffffffffffffffffff0000ffff";
   "XMM12", "0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0";
   "XMM13", "0x40404040"];;

let kp4_consts s =
  String.concat " /\\\n"
   (map (fun (r,v) -> Printf.sprintf "read %s %s = word %s" r s v) KPPACK4_CONSTS);;

(* ------------------------------------------------------------------------- *)
(* PACKUSWB. The simulation gives its result as the number made of the 16    *)
(* saturated bytes word(MIN (if bit 15 w then 0 else val w) 255) of the      *)
(* 16-bit lanes w. In this loop no lane is saturated, which bit-blasting     *)
(* shows for each lane w (KP4_SAT_CONV), so the byte is word_zx w, and the  *)
(* number is the join of the bytes (KP4_PACKUSWB_JOIN, the PACKUSWB_JOIN of  *)
(* x86/proofs/utils/mlkem_native_image.ml, which the mldsa proofs do not     *)
(* load). KP4_TIDY_TAC puts the YMM facts with a PACKUSWB in that form.      *)
(* ------------------------------------------------------------------------- *)

let KP4_SAT_LE = prove
 (`!w:int16. ~bit 15 w /\ word_ule w (word 255)
             ==> word(MIN (if bit 15 w then 0 else val w) 255):byte = word_zx w`,
  GEN_TAC THEN REWRITE_TAC[WORD_ULE; VAL_WORD; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN ASM_REWRITE_TAC[word_zx] THEN
  AP_TERM_TAC THEN ASM_ARITH_TAC);;

let KP4_SAT_CONV =
  let pat = `word(MIN (if bit 15 (w:int16) then 0 else val w) 255):byte` in
  fun tm ->
    let w = try rand(rand(lhand(rand tm))) with Failure _ -> failwith "KP4_SAT_CONV" in
    if type_of w <> `:int16` || not (aconv (vsubst [w,`w:int16`] pat) tm)
    then failwith "KP4_SAT_CONV" else
    let c = vsubst [w,`w:int16`] `~bit 15 (w:int16) /\ word_ule w (word 255)` in
    let th = try BITBLAST_RULE c
             with Failure _ -> failwith ("KP4_SAT_CONV: a lane may saturate: " ^ string_of_term w) in
    MP (SPEC w KP4_SAT_LE) th;;

let KP4_PACKUSWB_JOIN = prove
 (`!(b0:byte) (b1:byte) (b2:byte) (b3:byte) (b4:byte) (b5:byte) (b6:byte)
    (b7:byte) (b8:byte) (b9:byte) (b10:byte) (b11:byte) (b12:byte)
    (b13:byte) (b14:byte) (b15:byte).
     word((val b0 * 1 + val b1 * 256 + val b2 * 65536 + val b3 * 16777216 +
           val b4 * 4294967296 + val b5 * 1099511627776 +
           val b6 * 281474976710656 + val b7 * 72057594037927936) +
          val b8 * 2 EXP 64 + val b9 * 4722366482869645213696 +
          val b10 * 1208925819614629174706176 +
          val b11 * 309485009821345068724781056 +
          val b12 * 79228162514264337593543950336 +
          val b13 * 20282409603651670423947251286016 +
          val b14 * 5192296858534827628530496329220096 +
          val b15 * 1329227995784915872903807060280344576):int128 =
     word_join
      (word_join (word_join (word_join b15 b14:int16)
                            (word_join b13 b12:int16):int32)
                 (word_join (word_join b11 b10:int16)
                            (word_join b9 b8:int16):int32):int64)
      (word_join (word_join (word_join b7 b6:int16)
                            (word_join b5 b4:int16):int32)
                 (word_join (word_join b3 b2:int16)
                            (word_join b1 b0:int16):int32):int64)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  SIMP_TAC[VAL_WORD_JOIN_SIMPLE; DIMINDEX_8; DIMINDEX_16; DIMINDEX_32;
           DIMINDEX_64; DIMINDEX_128; ARITH] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_128] THEN
  MAP_EVERY (fun t -> MP_TAC(ISPEC t VAL_BOUND))
   (map (fun k -> mk_var("b"^string_of_int k,`:byte`)) (0--15)) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MAP_EVERY (fun k ->
    SPEC_TAC(mk_comb(`val:byte->num`,mk_var("b"^string_of_int k,`:byte`)),
             mk_var("n"^string_of_int k,`:num`))) (0--15) THEN
  REPEAT STRIP_TAC THEN
  W(fun (_,w) -> MP_TAC(SPECL [lhand(lhand w);
    `340282366920938463463374607431768211456`] MOD_LT)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ARITH_TAC);;

let KP4_TIDY_TAC =
  let is_min t = try fst(dest_const(rator t)) = "MIN" with Failure _ -> false in
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_eq c && can (term_match [] `read (r:(x86state,int256)component) s`) (lhs c) &&
       can (find_term is_min) c
    then CONV_RULE(RAND_CONV(DEPTH_CONV KP4_SAT_CONV THENC
                             REWRITE_CONV[KP4_PACKUSWB_JOIN] THENC
                             SIMD_SIMPLIFY_CONV [])) th
    else th);;

(* the steps of the body, with KP4_TIDY_TAC after each *)
let KP4_STEPS_TAC execth ns =
  MAP_EVERY (fun n -> VERIF_SSE_STEPS_TAC execth [n] THEN KP4_TIDY_TAC) ns;;

(* RAX = word (a0 + 8 i), written without the 0 for a0 = 0 *)
let kp4_lin a0 = if a0 = 0 then "8 * i" else Printf.sprintf "%d + 8 * i" a0;;

let KPPACK4_STMT fn loop exit a0 dl ds =
  let cb = dl + 8 * a0 and ob = ds + a0 in
  parse_term(subst_tokens
   ["@MC@",image_mc; "@FN@",fn; "@L@",loop; "@X@",exit;
    "@A0@",string_of_int a0; "@OB@",string_of_int ob; "@CB@",string_of_int cb;
    "@XC@",kp4_consts "s"]
  "exists f_events.
  forall e rb rsp0 pc (x:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    aligned 16 (word_add rsp0 (word @CB@)) /\\
    ALL (nonoverlapping (word_add rb (word @OB@),128))
        [(word pc,libmldsa_size); (word_add rsp0 (word @CB@),1024)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) @MC@ /\\
              read RIP s = word (pc + @FN@_@L@) /\\
              read RSP s = rsp0 /\\ read RBX s = rb /\\ read RAX s = word @A0@ /\\
              @XC@ /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (@CB@ + 4 * i)))) s = x i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + @FN@_@X@) /\\
              read RSP s = rsp0 /\\
              (!j. j < 128 ==> read (memory :> bytes8 (word_add rb (word (@OB@ + j)))) s =
                               mld_polyeta_pack_4 x j) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rb rsp0 pc /\\
                 memaccess_inbounds e2 [word_add rsp0 (word @CB@),1024; word_add rb (word @OB@),128]
                                       [word_add rb (word @OB@),128]))
         (MAYCHANGE [RIP; RAX] ,, MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes(word_add rb (word @OB@),128)])");;

let KPPACK4_INV a0 dl ds =
  let cb = dl + 8 * a0 and ob = ds + a0 in
  parse_term(subst_tokens
   ["@LIN@",kp4_lin a0; "@OB@",string_of_int ob; "@CB@",string_of_int cb;
    "@XC@",kp4_consts "s"]
  "\\i s. read RSP s = rsp0 /\\ read RBX s = rb /\\ read RAX s = word (@LIN@) /\\
         @XC@ /\\
         (!j. j < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (@CB@ + 4 * j)))) s = (x:num->int32) j) /\\
         (!j. j < 8 * i ==> read (memory :> bytes8 (word_add rb (word (@OB@ + j)))) s =
                            mld_polyeta_pack_4 x j)");;

(* the address of [rsp + rax * 8 + d] and [rbx + rax + d] as the simulation
   writes it, with RAX = word lin *)
let kp4_sim_form k lin d =
  if d < 0 then
    Printf.sprintf "%s(%s) + %s" (if k = 1 then "1 * " else Printf.sprintf "%d * " k) lin
      (Num.string_of_num (Num.add_num (Num.power_num (Num.num_of_int 2) (Num.num_of_int 64)) (Num.num_of_int d)))
  else if d = 0 then Printf.sprintf "%d * (%s)" k lin
  else Printf.sprintf "%d * (%s) + %d" k lin d;;

(* the canonical forms of the addresses, s * i + c as LIN2_ADDR_CONV s *)
let kp4_can s c = if c = 0 then Printf.sprintf "%d * i" s else Printf.sprintf "%d * i + %d" s c;;

let kp4_alias p sim can =
  SUBGOAL_THEN (parse_term(Printf.sprintf
    "word_add (%s:int64) (word (%s)) = word_add %s (word (%s))" p sim p can))
    ASSUME_TAC THENL [CP_ALIAS64_TAC; ALL_TAC];;

(* the stores of the iteration as facts about their bytes *)
let KP4_SPLIT_STORES_TAC sn ob =
  MAP_EVERY (fun c ->
    let lhs_tm = parse_term(Printf.sprintf
      "read (memory :> bytes32 (word_add (rb:int64) (word (%s)))) (%s:x86state)" (kp4_can 8 (ob + c)) sn) in
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(SIMD_SIMPLIFY_CONV []) o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (fun th -> is_eq(concl th) && aconv (lhs(concl th)) lhs_tm))) [0;4];;

(* the coefficients of the polynomial in the goal as x(16 * i + c) *)
let KP4_SPEC_TAC =
  REWRITE_TAC[mld_polyeta_pack_4] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV (LIN2_ADDR_CONV 16)) THEN
  REPEAT CONJ_TAC THEN APP_BLAST_TAC `x:num->int32`;;

let KPPACK4_BODY_TAC execth a0 dl ds =
  let cb = dl + 8 * a0 and ob = ds + a0 in
  let lin = kp4_lin a0 in
  let ars = [ARITH_RULE (parse_term(Printf.sprintf "%s = (%s) + 8"
                (if a0 = 0 then "8 * (i + 1)" else Printf.sprintf "%d + 8 * (i + 1)" a0) lin))] in
  MAP_EVERY (fun n -> GHOST_INTRO_TAC (mk_var(Printf.sprintf "ymm%d_g" n,`:int256`))
                       (parse_term(Printf.sprintf "read YMM%d" n))) (0--7) THEN
  FULL_INIT_TAC THEN
  MAP_EVERY (fun n -> XMM_EXISTSTOP_TAC (Printf.sprintf "top%d" n) (parse_term(Printf.sprintf "YMM%d" n))) (8--13) THEN
  VAL_INT64_TAC (parse_term lin) THEN
  (* aliases and alignment of the loads and stores *)
  MAP_EVERY (fun q ->
    let sim = kp4_sim_form 8 lin (dl + 16 * q) and can = kp4_can 64 (cb + 16 * q) in
    kp4_alias "rsp0" sim can THEN
    ALIGN16_IDX_TAC `rsp0:int64` (parse_term can) THEN
    (if dl + 16 * q < 0 then ALL_TAC
     else ALIGN16_IDX_TAC `rsp0:int64` (parse_term sim))) (0--3) THEN
  MAP_EVERY (fun c ->
    kp4_alias "rb" (kp4_sim_form 1 lin (ds + c)) (kp4_can 8 (ob + c))) [0;4] THEN
  (* the 16 coefficients of the iteration, merged into the four vectors *)
  SUBGOAL_THEN (parse_term(Printf.sprintf
    "!k. k < 16 ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * (16 * i + k))))) s0 = (x:num->int32)(16 * i + k)" cb))
    MP_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`i < 16`; `k < 16`] THEN ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN STRIP_TAC THEN RL_ADDR_LINEAR_TAC 64 THEN
  MAP_EVERY (fun q ->
    RL_MERGE_TAC 2 64 (parse_term(Printf.sprintf
      "read(memory :> bytes128(word_add rsp0 (word (%s)))) s0" (kp4_can 64 (cb + 16 * q))))) (0--3) THEN
  KP4_STEPS_TAC execth (1--54) THEN X86_STEPS_TAC execth (55--57) THEN
  RL_ADDR_LINEAR_TAC 8 THEN
  KP4_SPLIT_STORES_TAC "s57" ob THEN
  RL_FULL_FINAL_TAC 8 8 ars
   (REWRITE_TAC[XMM8; XMM9; XMM10; XMM11; XMM12; XMM13; READ_ZEROTOP_128] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST)
   KP4_SPEC_TAC;;

let KPPACK4_EXEC fn loop exit = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))];;

let KPPACK4_TAC fn loop exit a0 dl ds =
  let execth = KPPACK4_EXEC fn loop exit in
  CONCRETIZE_F_EVENTS_TAC
   `\(rb:int64) (rsp0:int64) (pc:num).
      APPEND (f_ev_epil rb rsp0 pc)
       (APPEND (ENUMERATEL 16 (\i. f_ev_loop rb rsp0 pc i)) (f_ev_prol rb rsp0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rb:int64`; `rsp0:int64`; `pc:num`; `x:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `16`
   (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (KPPACK4_INV a0 dl ds) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0; ADD_CLAUSES] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    KPPACK4_BODY_TAC execth a0 dl ds;
    FULL_EXIT0_TAC];;

let PROVE_KPPACK4 fn loop exit a0 dl ds =
  prove(KPPACK4_STMT fn loop exit a0 dl ds, KPPACK4_TAC fn loop exit a0 dl ds);;
