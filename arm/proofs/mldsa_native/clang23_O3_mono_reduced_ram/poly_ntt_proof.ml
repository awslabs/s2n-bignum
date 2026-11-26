(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Forward number-theoretic transform: the proof (see poly_ntt_spec.ml).     *)
(* The function is 12 loops, one or more per layer of the transform (see     *)
(* inline_ntt.ml for the lemmas of the loops), with a few instructions       *)
(* between them that set the registers. The proof composes the lemmas of the *)
(* loops: after each loop, the polynomial is the result of the blocks done   *)
(* of the layer (mld_ntt_blocks), and at the end of a layer the result of    *)
(* the layers done (mld_ntt_layers). The zetas of the first three layers are *)
(* in immediates and numerals in the lemmas; mld_zeta gives them as words.   *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_ntt_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_ntt.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_polyvec.ml";;

(* ------------------------------------------------------------------------- *)
(* The loops: their registers, addresses and constants (see inline_ntt.ml).  *)
(* ------------------------------------------------------------------------- *)

let NTT_EXEC = MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;

let NTT_MC = "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc";;


let ntt_loop1 = { loop = "mldsa_poly_ntt_loop1"; exit = "mldsa_poly_ntt_loop1_exit";
  ptr = "X9"; k0 = 4; cnt = "X10"; start = 0; len = 128; z = 25847;
  consts = ["X8","7863079302059786240"; "X11","25847"; "X12","18446744073701171199"];
  steps = 23;
  lo0 = "word_add a (word_sub (word (4 + 8 * i)) (word 4))"; lo1 = "word_add a (word_sub (word (4 + 8 * i)) (word 0))";
  up0 = "word_add a (word ((4 + 8 * i) + 508))"; up1 = "word_add a (word ((4 + 8 * i) + 512))";
  wsub = [4,4; 4,0] };;
let ntt_loop2 = { loop = "mldsa_poly_ntt_loop2"; exit = "mldsa_poly_ntt_loop2_exit";
  ptr = "X10"; k0 = 4; cnt = "X11"; start = 0; len = 64; z = -2608894;
  consts = ["X8","18446744073706942722"; "X9","10157993212938027008"; "X12","18446744073701171199"]; steps = 21;
  lo0 = "word_add a (word_sub (word (4 + 8 * i)) (word 4))"; lo1 = "word_add a (word_sub (word (4 + 8 * i)) (word 0))"; up0 = "word_add a (word ((4 + 8 * i) + 252))"; up1 = "word_add a (word ((4 + 8 * i) + 256))";
  wsub = [4,4; 4,0] };;
let ntt_loop3 = { loop = "mldsa_poly_ntt_loop3"; exit = "mldsa_poly_ntt_loop3_exit";
  ptr = "X10"; k0 = 512; cnt = "X11"; start = 128; len = 64; z = -518909;
  consts = ["X8","18446744073709032707"; "X9","10167004814534246400"; "X12","18446744073701171199"]; steps = 22;
  lo0 = "word_add a (word (512 + 8 * i))"; lo1 = "word_add a (word ((512 + 8 * i) + 4))"; up0 = "word_add a (word ((512 + 8 * i) + 256))"; up1 = "word_add a (word ((512 + 8 * i) + 260))";
  wsub = [] };;
let ntt_loop4 = { loop = "mldsa_poly_ntt_loop4"; exit = "mldsa_poly_ntt_loop4_exit";
  ptr = "X10"; k0 = 4; cnt = "X11"; start = 0; len = 32; z = 237124;
  consts = ["X8","7047040794334593024"; "X9","237124"; "X12","18446744073701171199"]; steps = 21;
  lo0 = "word_add a (word_sub (word (4 + 8 * i)) (word 4))"; lo1 = "word_add a (word_sub (word (4 + 8 * i)) (word 0))"; up0 = "word_add a (word ((4 + 8 * i) + 124))"; up1 = "word_add a (word ((4 + 8 * i) + 128))";
  wsub = [4,4; 4,0] };;
let ntt_loop5 = { loop = "mldsa_poly_ntt_loop5"; exit = "mldsa_poly_ntt_loop5_exit";
  ptr = "X10"; k0 = 388; cnt = "X11"; start = 64; len = 32; z = -777960;
  consts = ["X8","18446744073708773656"; "X9","6347578586764935168"; "X12","18446744073701171199"]; steps = 21;
  lo0 = "word_add a (word_sub (word (388 + 8 * i)) (word 132))"; lo1 = "word_add a (word_sub (word (388 + 8 * i)) (word 128))"; up0 = "word_add a (word_sub (word (388 + 8 * i)) (word 4))"; up1 = "word_add a (word_sub (word (388 + 8 * i)) (word 0))";
  wsub = [388,4; 388,0; 388,132; 388,128] };;
let ntt_loop6 = { loop = "mldsa_poly_ntt_loop6"; exit = "mldsa_poly_ntt_loop6_exit";
  ptr = "X10"; k0 = 644; cnt = "X11"; start = 128; len = 32; z = -876248;
  consts = ["X8","18446744073708675368"; "X9","6924180145276190720"; "X12","18446744073701171199"]; steps = 21;
  lo0 = "word_add a (word_sub (word (644 + 8 * i)) (word 132))"; lo1 = "word_add a (word_sub (word (644 + 8 * i)) (word 128))"; up0 = "word_add a (word_sub (word (644 + 8 * i)) (word 4))"; up1 = "word_add a (word_sub (word (644 + 8 * i)) (word 0))";
  wsub = [644,4; 644,0; 644,132; 644,128] };;
let ntt_loop7 = { loop = "mldsa_poly_ntt_loop7"; exit = "mldsa_poly_ntt_loop7_exit";
  ptr = "X10"; k0 = 900; cnt = "X11"; start = 192; len = 32; z = 466468;
  consts = ["X8","7046899919407284224"; "X9","466468"; "X12","18446744073701171199"]; steps = 21;
  lo0 = "word_add a (word_sub (word (900 + 8 * i)) (word 132))"; lo1 = "word_add a (word_sub (word (900 + 8 * i)) (word 128))"; up0 = "word_add a (word_sub (word (900 + 8 * i)) (word 4))"; up1 = "word_add a (word_sub (word (900 + 8 * i)) (word 0))";
  wsub = [900,4; 900,0; 900,132; 900,128] };;
let ntt_bloop8 = { bloop = "mldsa_poly_ntt_loop8"; bexit = "mldsa_poly_ntt_loop8_exit"; lay = 3; blen = 16;
  bptr = "X11"; bk0 = 64; bstep = 128; bidx = "X10";
  bconsts = ["X8","(pc + rodata_mld_zetas)"; "X9","252236767799803904"; "X12","18446744073701171199"]; bsteps = 150;
  bops = ["word_add a (word_sub (word (64 + 128 * i)) (word 64))",0; "word_add a (word_sub (word (64 + 128 * i)) (word 60))",1; "word_add a (word_sub (word (64 + 128 * i)) (word 56))",2; "word_add a (word_sub (word (64 + 128 * i)) (word 52))",3; "word_add a (word_sub (word (64 + 128 * i)) (word 48))",4; "word_add a (word_sub (word (64 + 128 * i)) (word 44))",5; "word_add a (word_sub (word (64 + 128 * i)) (word 40))",6; "word_add a (word_sub (word (64 + 128 * i)) (word 36))",7; "word_add a (word_sub (word (64 + 128 * i)) (word 32))",8; "word_add a (word_sub (word (64 + 128 * i)) (word 28))",9; "word_add a (word_sub (word (64 + 128 * i)) (word 24))",10; "word_add a (word_sub (word (64 + 128 * i)) (word 20))",11; "word_add a (word_sub (word (64 + 128 * i)) (word 16))",12; "word_add a (word_sub (word (64 + 128 * i)) (word 12))",13; "word_add a (word_sub (word (64 + 128 * i)) (word 8))",14; "word_add a (word_sub (word (64 + 128 * i)) (word 4))",15; "word_add a (word (64 + 128 * i))",16; "word_add a (word ((64 + 128 * i) + 4))",17; "word_add a (word ((64 + 128 * i) + 8))",18; "word_add a (word ((64 + 128 * i) + 12))",19; "word_add a (word ((64 + 128 * i) + 16))",20; "word_add a (word ((64 + 128 * i) + 20))",21; "word_add a (word ((64 + 128 * i) + 24))",22; "word_add a (word ((64 + 128 * i) + 28))",23; "word_add a (word ((64 + 128 * i) + 32))",24; "word_add a (word ((64 + 128 * i) + 36))",25; "word_add a (word ((64 + 128 * i) + 40))",26; "word_add a (word ((64 + 128 * i) + 44))",27; "word_add a (word ((64 + 128 * i) + 48))",28; "word_add a (word ((64 + 128 * i) + 52))",29; "word_add a (word ((64 + 128 * i) + 56))",30; "word_add a (word ((64 + 128 * i) + 60))",31];
  bzaddr = "word_add (word (pc + rodata_mld_zetas)) (word (4 * i + 32))"; bwsub = [64,4; 64,8; 64,12; 64,16; 64,20; 64,24; 64,28; 64,32; 64,36; 64,40; 64,44; 64,48; 64,52; 64,56; 64,60; 64,64];
  bregs = ["X1"; "X2"; "X3"; "X4"; "X5"; "X6"; "X7"; "X13"; "X14"; "X15"; "X16"; "X17"; "X18"; "X19"; "X20"; "X21"; "X22"; "X23"; "X24"] };;
let ntt_bloop9 = { bloop = "mldsa_poly_ntt_loop9"; bexit = "mldsa_poly_ntt_loop9_exit"; lay = 4; blen = 8;
  bptr = "X11"; bk0 = 32; bstep = 64; bidx = "X10";
  bconsts = ["X8","(pc + rodata_mld_zetas)"; "X9","252236767799803904"; "X12","18446744073701171199"]; bsteps = 78;
  bops = ["word_add a (word_sub (word (32 + 64 * i)) (word 32))",0; "word_add a (word_sub (word (32 + 64 * i)) (word 28))",1; "word_add a (word_sub (word (32 + 64 * i)) (word 24))",2; "word_add a (word_sub (word (32 + 64 * i)) (word 20))",3; "word_add a (word_sub (word (32 + 64 * i)) (word 16))",4; "word_add a (word_sub (word (32 + 64 * i)) (word 12))",5; "word_add a (word_sub (word (32 + 64 * i)) (word 8))",6; "word_add a (word_sub (word (32 + 64 * i)) (word 4))",7; "word_add a (word (32 + 64 * i))",8; "word_add a (word ((32 + 64 * i) + 4))",9; "word_add a (word ((32 + 64 * i) + 8))",10; "word_add a (word ((32 + 64 * i) + 12))",11; "word_add a (word ((32 + 64 * i) + 16))",12; "word_add a (word ((32 + 64 * i) + 20))",13; "word_add a (word ((32 + 64 * i) + 24))",14; "word_add a (word ((32 + 64 * i) + 28))",15];
  bzaddr = "word_add (word (pc + rodata_mld_zetas)) (word (4 * i + 64))"; bwsub = [32,4; 32,8; 32,12; 32,16; 32,20; 32,24; 32,28; 32,32];
  bregs = ["X1"; "X2"; "X3"; "X4"; "X5"; "X6"; "X7"; "X13"; "X14"; "X15"; "X16"; "X17"; "X18"; "X19"] };;
let ntt_bloop10 = { bloop = "mldsa_poly_ntt_loop10"; bexit = "mldsa_poly_ntt_loop10_exit"; lay = 5; blen = 4;
  bptr = "X11"; bk0 = 16; bstep = 32; bidx = "X10";
  bconsts = ["X8","(pc + rodata_mld_zetas)"; "X9","252236767799803904"; "X12","18446744073701171199"]; bsteps = 42;
  bops = ["word_add a (word_sub (word (16 + 32 * i)) (word 16))",0; "word_add a (word_sub (word (16 + 32 * i)) (word 12))",1; "word_add a (word_sub (word (16 + 32 * i)) (word 8))",2; "word_add a (word_sub (word (16 + 32 * i)) (word 4))",3; "word_add a (word (16 + 32 * i))",4; "word_add a (word ((16 + 32 * i) + 4))",5; "word_add a (word ((16 + 32 * i) + 8))",6; "word_add a (word ((16 + 32 * i) + 12))",7];
  bzaddr = "word_add (word (pc + rodata_mld_zetas)) (word (4 * i + 128))"; bwsub = [16,4; 16,8; 16,12; 16,16];
  bregs = ["X1"; "X2"; "X13"; "X14"; "X15"; "X16"; "X17"; "X18"] };;

(* ------------------------------------------------------------------------- *)
(* The loops as lemmas: loops 1 to 10 are generated, 11 and 12 are in        *)
(* inline_ntt.ml.                                                            *)
(* ------------------------------------------------------------------------- *)

let NTT_LS =
  map (fun p -> NTT_CLOOP NTT_MC NTT_EXEC p)
      [ntt_loop1; ntt_loop2; ntt_loop3; ntt_loop4; ntt_loop5; ntt_loop6; ntt_loop7] @
  map (fun p -> NTT_BLOOP NTT_MC NTT_EXEC p)
      [ntt_bloop8; ntt_bloop9; ntt_bloop10] @
  [NTT_LOOP11; NTT_LOOP12];;

(*** The zetas of the first layers as numerals ***)

let NTT_ZETA k =
  (REWRITE_CONV[mld_zeta; mld_zetas] THENC RAND_CONV EL_CONV THENC WORD_REDUCE_CONV)
    (mk_comb(`mld_zeta`, mk_small_numeral k));;
let NTT_ZETAS = map NTT_ZETA (1--7);;

(*** The layers and blocks one step at a time ***)

let NTT_LAYER_UNF n =
  CONV_RULE NUM_REDUCE_CONV
   (INST [mk_small_numeral(n-1),`l:num`] (SPEC_ALL (CONJUNCT2 mld_ntt_layers)));;
let NTT_BLOCKS_UNF l b =
  CONV_RULE NUM_REDUCE_CONV
   (INST [mk_small_numeral l,`l:num`; mk_small_numeral(b-1),`b:num`]
         (SPEC_ALL (CONJUNCT2 mld_ntt_blocks)));;

(*** The block of a loop as a step of the layers ***)

let ntt_zw k = string_of_num(dest_numeral(rand(rand(concl(el (k-1) NTT_ZETAS)))));;

let NTT_BR zk s len in_s out_s unfs =
  prove(parse_term(Printf.sprintf "mld_ntt_block (word %s) %d %d (%s) = (%s)"
                     (ntt_zw zk) s len in_s out_s),
        REWRITE_TAC (unfs @ [el (zk-1) NTT_ZETAS; CONJUNCT1 mld_ntt_blocks;
                             CONJUNCT1 mld_ntt_layers]));;

let NTT_BRS =
  [NTT_BR 1 0 128 "x" "mld_ntt_layers 1 x" [NTT_LAYER_UNF 1; NTT_BLOCKS_UNF 0 1];
   NTT_BR 2 0 64 "mld_ntt_layers 1 x" "mld_ntt_blocks 1 1 (mld_ntt_layers 1 x)"
     [NTT_BLOCKS_UNF 1 1];
   NTT_BR 3 128 64 "mld_ntt_blocks 1 1 (mld_ntt_layers 1 x)" "mld_ntt_layers 2 x"
     [NTT_LAYER_UNF 2; NTT_BLOCKS_UNF 1 2];
   NTT_BR 4 0 32 "mld_ntt_layers 2 x" "mld_ntt_blocks 2 1 (mld_ntt_layers 2 x)"
     [NTT_BLOCKS_UNF 2 1];
   NTT_BR 5 64 32 "mld_ntt_blocks 2 1 (mld_ntt_layers 2 x)"
     "mld_ntt_blocks 2 2 (mld_ntt_layers 2 x)" [NTT_BLOCKS_UNF 2 2];
   NTT_BR 6 128 32 "mld_ntt_blocks 2 2 (mld_ntt_layers 2 x)"
     "mld_ntt_blocks 2 3 (mld_ntt_layers 2 x)" [NTT_BLOCKS_UNF 2 3];
   NTT_BR 7 192 32 "mld_ntt_blocks 2 3 (mld_ntt_layers 2 x)" "mld_ntt_layers 3 x"
     [NTT_LAYER_UNF 3; NTT_BLOCKS_UNF 2 4]];;

(*** The loops of the layers 4 to 8 do all the blocks of the layer ***)

let NTT_LAYS = map (fun l -> GSYM(NTT_LAYER_UNF (l+1))) (3--7);;

(* ------------------------------------------------------------------------- *)
(* The composition of the loops.                                             *)
(* ------------------------------------------------------------------------- *)


let NTT_APPEND_CONG = prove
 (`!(a:(A)list) b c d. a = c /\ b = d ==> APPEND a b = APPEND c d`,
  MESON_TAC[]);;

let NTT_EVENTS_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[APPEND_NIL; CONJUNCT1 APPEND; GSYM APPEND_ASSOC] THEN
    REPEAT(MATCH_MP_TAC NTT_APPEND_CONG THEN CONJ_TAC THENL
            [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]) THEN
    FULL_UNIFY_F_EVENTS_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[APPEND_NIL; CONJUNCT1 APPEND; GSYM APPEND_ASSOC] THEN
  DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

(*** The input function of loop k and the layer of its output ***)

let NTT_INPUTS =
  [`x:num->int32`; `mld_ntt_layers 1 x`; `mld_ntt_blocks 1 1 (mld_ntt_layers 1 x)`;
   `mld_ntt_layers 2 x`; `mld_ntt_blocks 2 1 (mld_ntt_layers 2 x)`;
   `mld_ntt_blocks 2 2 (mld_ntt_layers 2 x)`; `mld_ntt_blocks 2 3 (mld_ntt_layers 2 x)`;
   `mld_ntt_layers 3 x`; `mld_ntt_layers 4 x`; `mld_ntt_layers 5 x`;
   `mld_ntt_layers 6 x`; `mld_ntt_layers 7 x`];;

(*** The instructions between the loops (and before the first, after the last) ***)

let NTT_PRE = [9; 7; 7; 7; 7; 7; 7; 7; 3; 3; 6; 5];;
let NTT_EPI = 23;;

let NTT_FULL_TAC =
  let hname k = "H_L"^string_of_int k in
  let args = "a pc stackpointer returnaddress" in
  let template = parse_term(Printf.sprintf
   "\\(a:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      APPEND (f_ev_epi %s) %s :(uarch_event)list"
    args
    (let rec build k =
       if k = 0 then Printf.sprintf "(f_ev_pro %s)" args
       else Printf.sprintf "(APPEND (f_ev_l%d %s) %s)" k args (build (k-1)) in
     build 12)) in
  let call k s =
    FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc NTT_EXEC (hname k)
     [`a:int64`; el (k-1) NTT_INPUTS; `pc:num`]
     [`pc:num`; `a:int64`; `stackpointer:int64`; `returnaddress:int64`] (s + 1) in
  let bridge k =
    if k <= 7 then RULE_ASSUM_TAC(REWRITE_RULE[el (k-1) NTT_BRS])
    else if k <= 12 && k >= 8 then RULE_ASSUM_TAC(REWRITE_RULE[el (k-8) NTT_LAYS])
    else ALL_TAC in
  let steps_before k t =
    (* the instructions before loop k, from state t; the adrp of loop 8 is 5th *)
    let m = el (k-1) NTT_PRE in
    if k = 8 then
      ARM_STEPS_TAC NTT_EXEC ((t+1) -- (t+5)) THEN MLKEM_NATIVE_ADRP_TAC THEN
      ARM_STEPS_TAC NTT_EXEC ((t+6) -- (t+7)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `247592`] WORD_ADD])
    else ARM_STEPS_TAC NTT_EXEC ((t+1) -- (t+m)) in
  MAP_EVERY (fun k -> ASSUME_CALLEE_SAFETY_TAILED_TAC (el (k-1) NTT_LS) (hname k))
            (1 -- 12) THEN
  CONCRETIZE_F_EVENTS_TAC template THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst NTT_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun k -> ENSURES_PRESERVED_TAC (Printf.sprintf "x%d_init" k) (parse_term (Printf.sprintf "X%d" k))) (19--24) THEN
  FULL_INIT_TAC THEN
  (let rec go k t =
     if k > 12 then
       ARM_STEPS_TAC NTT_EXEC ((t+1) -- (t+NTT_EPI)) THEN
       ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[mld_poly_ntt] THEN
       RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `247592`] WORD_ADD]) THEN
       NTT_EVENTS_TAC
     else
       steps_before k t THEN
       (let t' = t + el (k-1) NTT_PRE in
        (if k = 1 then
           VEC_REST_TAC (parse_term(Printf.sprintf "!i. i < 256 ==> read (memory :> bytes32 (word_add a (word (4 * i)))) s%d = (x:num->int32) i" t'))
         else ALL_TAC) THEN
        call k t' THEN
        (if k = 1 then RULE_ASSUM_TAC(REWRITE_RULE[CONJUNCT1 APPEND]) else ALL_TAC) THEN
        bridge k THEN
        go (k+1) (t'+1)) in
   go 1 0);;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety.                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  NTT_FULL_TAC);;

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
