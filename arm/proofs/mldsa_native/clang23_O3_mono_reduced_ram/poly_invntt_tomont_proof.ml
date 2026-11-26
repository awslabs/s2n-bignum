(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Inverse number-theoretic transform: the proof (see                        *)
(* poly_invntt_tomont_spec.ml). The function is 13 loops (see                *)
(* inline_invntt.ml for the lemmas of the loops), with a few instructions    *)
(* between them that set the registers: after each loop, the polynomial is   *)
(* rewritten to the blocks or layers of mld_invntt_layers that are done. The *)
(* zetas of the last layers are numerals in the lemmas and are tied to       *)
(* mld_zeta by a conversion on the table. Layers 3 to 5 spill to the stack   *)
(* and the address of the polynomial is kept in the frame between them.      *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_invntt.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_polyvec.ml";;

let INV_MC = "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc";;

(* ------------------------------------------------------------------------- *)
(* The loops: their registers, addresses and constants (see inline_invntt.ml).*)
(* ------------------------------------------------------------------------- *)

let inv_loop6 = { iloop = "mldsa_poly_invntt_tomont_loop6"; iexit = "mldsa_poly_invntt_tomont_loop6_exit";
  iptr = "X10"; ik0 = 132; icnt = "X11"; istart = 0; ilen = 32; iz = -466468;
  iconsts = ["X8","18446744073709085148"; "X9","11399844154302267392"; "X12","18446744073701171199"]; isteps = 23;
  ilo0 = "word_add a (word_sub (word (132 + 8 * i)) (word 132))"; ilo1 = "word_add a (word_sub (word (132 + 8 * i)) (word 128))";
  iup0 = "word_add a (word_sub (word (132 + 8 * i)) (word 4))"; iup1 = "word_add a (word_sub (word (132 + 8 * i)) (word 0))";
  iwsub = [132,132; 132,128; 132,4; 132,0]; iregs = ["X0"; "X1"; "X13"; "X14"; "X15"; "X16"; "X17"; "X18"] };;
let inv_loop7 = { iloop = "mldsa_poly_invntt_tomont_loop7"; iexit = "mldsa_poly_invntt_tomont_loop7_exit";
  iptr = "X10"; ik0 = 388; icnt = "X11"; istart = 64; ilen = 32; iz = 876248;
  iconsts = ["X8","11522563928433360896"; "X9","876248"; "X12","18446744073701171199"]; isteps = 23;
  ilo0 = "word_add a (word_sub (word (388 + 8 * i)) (word 132))"; ilo1 = "word_add a (word_sub (word (388 + 8 * i)) (word 128))";
  iup0 = "word_add a (word_sub (word (388 + 8 * i)) (word 4))"; iup1 = "word_add a (word_sub (word (388 + 8 * i)) (word 0))";
  iwsub = [388,132; 388,128; 388,4; 388,0]; iregs = ["X0"; "X1"; "X13"; "X14"; "X15"; "X16"; "X17"; "X18"] };;
let inv_loop8 = { iloop = "mldsa_poly_invntt_tomont_loop8"; iexit = "mldsa_poly_invntt_tomont_loop8_exit";
  iptr = "X10"; ik0 = 644; icnt = "X11"; istart = 128; ilen = 32; iz = 777960;
  iconsts = ["X8","12099165486944616448"; "X9","777960"; "X12","18446744073701171199"]; isteps = 23;
  ilo0 = "word_add a (word_sub (word (644 + 8 * i)) (word 132))"; ilo1 = "word_add a (word_sub (word (644 + 8 * i)) (word 128))";
  iup0 = "word_add a (word_sub (word (644 + 8 * i)) (word 4))"; iup1 = "word_add a (word_sub (word (644 + 8 * i)) (word 0))";
  iwsub = [644,132; 644,128; 644,4; 644,0]; iregs = ["X0"; "X1"; "X13"; "X14"; "X15"; "X16"; "X17"; "X18"] };;
let inv_loop9 = { iloop = "mldsa_poly_invntt_tomont_loop9"; iexit = "mldsa_poly_invntt_tomont_loop9_exit";
  iptr = "X10"; ik0 = 900; icnt = "X11"; istart = 192; ilen = 32; iz = -237124;
  iconsts = ["X8","18446744073709314492"; "X9","11399703279374958592"; "X12","18446744073701171199"]; isteps = 23;
  ilo0 = "word_add a (word_sub (word (900 + 8 * i)) (word 132))"; ilo1 = "word_add a (word_sub (word (900 + 8 * i)) (word 128))";
  iup0 = "word_add a (word_sub (word (900 + 8 * i)) (word 4))"; iup1 = "word_add a (word_sub (word (900 + 8 * i)) (word 0))";
  iwsub = [900,132; 900,128; 900,4; 900,0]; iregs = ["X0"; "X1"; "X13"; "X14"; "X15"; "X16"; "X17"; "X18"] };;
let inv_loop10 = { iloop = "mldsa_poly_invntt_tomont_loop10"; iexit = "mldsa_poly_invntt_tomont_loop10_exit";
  iptr = "X10"; ik0 = 256; icnt = "X11"; istart = 0; ilen = 64; iz = 518909;
  iconsts = ["X8","8279739259175305216"; "X9","518909"; "X12","18446744073701171199"]; isteps = 22;
  ilo0 = "word_add a (word_sub (word (256 + 8 * i)) (word 256))"; ilo1 = "word_add a (word_sub (word (256 + 8 * i)) (word 252))";
  iup0 = "word_add a (word (256 + 8 * i))"; iup1 = "word_add a (word ((256 + 8 * i) + 4))";
  iwsub = [256,256; 256,252]; iregs = ["X0"; "X1"; "X13"; "X14"; "X15"; "X16"; "X17"; "X18"] };;
let inv_loop11 = { iloop = "mldsa_poly_invntt_tomont_loop11"; iexit = "mldsa_poly_invntt_tomont_loop11_exit";
  iptr = "X10"; ik0 = 512; icnt = "X11"; istart = 128; ilen = 64; iz = 2608894;
  iconsts = ["X8","8288750860771524608"; "X9","2608894"; "X12","18446744073701171199"]; isteps = 25;
  ilo0 = "word_add a (word (512 + 8 * i))"; ilo1 = "word_add a (word ((512 + 8 * i) + 4))";
  iup0 = "word_add a (word ((512 + 8 * i) + 256))"; iup1 = "word_add a (word ((512 + 8 * i) + 260))";
  iwsub = []; iregs = ["X0"; "X1"; "X13"; "X14"; "X15"; "X16"; "X17"; "X18"] };;
let inv_loop12 = { iloop = "mldsa_poly_invntt_tomont_loop12"; iexit = "mldsa_poly_invntt_tomont_loop12_exit";
  iptr = "X12"; ik0 = 0; icnt = "X9"; istart = 0; ilen = 128; iz = -25847;
  iconsts = ["X8","10583664771649765376"; "X10","18446744073701171199"; "X11","4294941449"]; isteps = 25;
  ilo0 = "word_add a (word (0 + 8 * i))"; ilo1 = "word_add a (word ((0 + 8 * i) + 4))";
  iup0 = "word_add a (word ((0 + 8 * i) + 512))"; iup1 = "word_add a (word ((0 + 8 * i) + 516))";
  iwsub = []; iregs = ["X0"; "X1"; "X13"; "X14"; "X15"; "X16"; "X17"; "X18"] };;
let inv_bloop3 = { bloop = "mldsa_poly_invntt_tomont_loop3"; bexit = "mldsa_poly_invntt_tomont_loop3_exit"; lay = 6;
  bptr = "X10"; bk0 = 16; bzptr = "X9"; bz0 = 252; bcnt = "X11"; bc0 = "18446744073709551608"; bcstep = 8;
  bconsts = ["X8","252236767799803904"; "X12","18446744073701171199"]; bsteps = 46;
  bops = ["word_add a (word_sub (word (16 + 32 * i)) (word 16))",0; "word_add a (word_sub (word (16 + 32 * i)) (word 12))",1; "word_add a (word_sub (word (16 + 32 * i)) (word 8))",2; "word_add a (word_sub (word (16 + 32 * i)) (word 4))",3; "word_add a (word (16 + 32 * i))",4; "word_add a (word ((16 + 32 * i) + 4))",5; "word_add a (word ((16 + 32 * i) + 8))",6; "word_add a (word ((16 + 32 * i) + 12))",7];
  bwsub = [16,4; 16,8; 16,12; 16,16]; bregs = ["X1"; "X2"; "X3"; "X4"; "X5"; "X6"; "X7"; "X13"; "X14"; "X15"; "X16"; "X17"; "X18"; "X19"; "X20"; "X21"; "X22"]; bsp = false };;
let inv_bloop4 = { bloop = "mldsa_poly_invntt_tomont_loop4"; bexit = "mldsa_poly_invntt_tomont_loop4_exit"; lay = 5;
  bptr = "X10"; bk0 = 32; bzptr = "X9"; bz0 = 124; bcnt = "X11"; bc0 = "18446744073709551600"; bcstep = 16;
  bconsts = ["X8","252236767799803904"; "X26","18446744073701171199"]; bsteps = 92;
  bops = ["word_add a (word_sub (word (32 + 64 * i)) (word 32))",0; "word_add a (word_sub (word (32 + 64 * i)) (word 28))",1; "word_add a (word_sub (word (32 + 64 * i)) (word 24))",2; "word_add a (word_sub (word (32 + 64 * i)) (word 20))",3; "word_add a (word_sub (word (32 + 64 * i)) (word 16))",4; "word_add a (word_sub (word (32 + 64 * i)) (word 12))",5; "word_add a (word_sub (word (32 + 64 * i)) (word 8))",6; "word_add a (word_sub (word (32 + 64 * i)) (word 4))",7; "word_add a (word (32 + 64 * i))",8; "word_add a (word ((32 + 64 * i) + 4))",9; "word_add a (word ((32 + 64 * i) + 8))",10; "word_add a (word ((32 + 64 * i) + 12))",11; "word_add a (word ((32 + 64 * i) + 16))",12; "word_add a (word ((32 + 64 * i) + 20))",13; "word_add a (word ((32 + 64 * i) + 24))",14; "word_add a (word ((32 + 64 * i) + 28))",15];
  bwsub = [32,4; 32,8; 32,12; 32,16; 32,20; 32,24; 32,28; 32,32]; bregs = ["X0"; "X1"; "X2"; "X3"; "X4"; "X5"; "X6"; "X7"; "X12"; "X13"; "X14"; "X15"; "X16"; "X17"; "X18"; "X19"; "X20"; "X21"; "X22"; "X23"; "X24"; "X25"; "X27"; "X28"; "X29"; "X30"]; bsp = false };;
let inv_bloop5 = { bloop = "mldsa_poly_invntt_tomont_loop5"; bexit = "mldsa_poly_invntt_tomont_loop5_exit"; lay = 4;
  bptr = "X10"; bk0 = 64; bzptr = "X11"; bz0 = 60; bcnt = "X27"; bc0 = "18446744073709551584"; bcstep = 32;
  bconsts = ["X8","252236767799803904"; "X12","18446744073701171199"]; bsteps = 201;
  bops = ["word_add a (word_sub (word (64 + 128 * i)) (word 64))",0; "word_add a (word_sub (word (64 + 128 * i)) (word 60))",1; "word_add a (word_sub (word (64 + 128 * i)) (word 56))",2; "word_add a (word_sub (word (64 + 128 * i)) (word 52))",3; "word_add a (word_sub (word (64 + 128 * i)) (word 48))",4; "word_add a (word_sub (word (64 + 128 * i)) (word 44))",5; "word_add a (word_sub (word (64 + 128 * i)) (word 40))",6; "word_add a (word_sub (word (64 + 128 * i)) (word 36))",7; "word_add a (word_sub (word (64 + 128 * i)) (word 32))",8; "word_add a (word_sub (word (64 + 128 * i)) (word 28))",9; "word_add a (word_sub (word (64 + 128 * i)) (word 24))",10; "word_add a (word_sub (word (64 + 128 * i)) (word 20))",11; "word_add a (word_sub (word (64 + 128 * i)) (word 16))",12; "word_add a (word_sub (word (64 + 128 * i)) (word 12))",13; "word_add a (word_sub (word (64 + 128 * i)) (word 8))",14; "word_add a (word_sub (word (64 + 128 * i)) (word 4))",15; "word_add a (word (64 + 128 * i))",16; "word_add a (word ((64 + 128 * i) + 4))",17; "word_add a (word ((64 + 128 * i) + 8))",18; "word_add a (word ((64 + 128 * i) + 12))",19; "word_add a (word ((64 + 128 * i) + 16))",20; "word_add a (word ((64 + 128 * i) + 20))",21; "word_add a (word ((64 + 128 * i) + 24))",22; "word_add a (word ((64 + 128 * i) + 28))",23; "word_add a (word ((64 + 128 * i) + 32))",24; "word_add a (word ((64 + 128 * i) + 36))",25; "word_add a (word ((64 + 128 * i) + 40))",26; "word_add a (word ((64 + 128 * i) + 44))",27; "word_add a (word ((64 + 128 * i) + 48))",28; "word_add a (word ((64 + 128 * i) + 52))",29; "word_add a (word ((64 + 128 * i) + 56))",30; "word_add a (word ((64 + 128 * i) + 60))",31];
  bwsub = [64,4; 64,8; 64,12; 64,16; 64,20; 64,24; 64,28; 64,32; 64,36; 64,40; 64,44; 64,48; 64,52; 64,56; 64,60; 64,64]; bregs = ["X0"; "X1"; "X2"; "X3"; "X4"; "X5"; "X6"; "X7"; "X9"; "X13"; "X14"; "X15"; "X16"; "X17"; "X18"; "X19"; "X20"; "X21"; "X22"; "X23"; "X24"; "X25"; "X26"; "X28"; "X29"; "X30"]; bsp = true };;

(* ------------------------------------------------------------------------- *)
(* The loops as lemmas.                                                      *)
(* ------------------------------------------------------------------------- *)

let INV_LS =
  [INV_V1_LOOP; INV_V2_LOOP] @
  map (fun p -> INV_BLOOP INV_MC INV_EXEC p) [inv_bloop3; inv_bloop4; inv_bloop5] @
  map (fun p -> INV_CLOOP INV_MC INV_EXEC p)
      [inv_loop6; inv_loop7; inv_loop8; inv_loop9; inv_loop10; inv_loop11; inv_loop12] @
  [INV_SCALE_LOOP];;

(* ------------------------------------------------------------------------- *)
(* The zetas of the last layers and the layers one step at a time.           *)
(* ------------------------------------------------------------------------- *)

let INV_NUMZETA k =
  (REWRITE_CONV[mld_zeta; mld_zetas] THENC RAND_CONV EL_CONV THENC WORD_REDUCE_CONV)
    (mk_comb(`mld_zeta`, mk_small_numeral k));;

let INV_ZETA k =
  let th = INV_NUMZETA k in
  let n = dest_numeral(rand(rhs(concl th))) in
  let two32 = Num.power_num (Num.num_of_int 2) (Num.num_of_int 32) in
  let m = Num.mod_num (Num.sub_num two32 n) two32 in
  prove(parse_term(Printf.sprintf "word_neg (mld_zeta %d) = (word %s:int32)" k (Num.string_of_num m)),
        REWRITE_TAC[th] THEN CONV_TAC WORD_REDUCE_CONV);;

let INV_ZETAS = map INV_ZETA (1--7);;

let INV_LAYER_UNF n =
  CONV_RULE NUM_REDUCE_CONV
   (INST [mk_small_numeral(n-1),`n:num`] (SPEC_ALL (CONJUNCT2 mld_invntt_layers)));;
let INV_BLOCKS_UNF l b =
  CONV_RULE NUM_REDUCE_CONV
   (INST [mk_small_numeral l,`m:num`; mk_small_numeral(b-1),`b:num`]
         (SPEC_ALL (CONJUNCT2 mld_invntt_blocks)));;

(*** The block of a loop with a numeral zeta as a step of the layers ***)

let INV_BR zk s len in_s out_s unfs =
  prove(parse_term(Printf.sprintf "mld_invntt_block (%s) %d %d (%s) = (%s)"
          (string_of_term(rhs(concl(el (zk-1) INV_ZETAS)))) s len in_s out_s),
        REWRITE_TAC (unfs @ [el (zk-1) INV_ZETAS; CONJUNCT1 mld_invntt_blocks;
                             CONJUNCT1 mld_invntt_layers]));;

let INV_BRS =
  [INV_BR 7 0 32 "mld_invntt_layers 5 x" "mld_invntt_blocks 3 1 (mld_invntt_layers 5 x)"
     [INV_BLOCKS_UNF 3 1];
   INV_BR 6 64 32 "mld_invntt_blocks 3 1 (mld_invntt_layers 5 x)"
     "mld_invntt_blocks 3 2 (mld_invntt_layers 5 x)" [INV_BLOCKS_UNF 3 2];
   INV_BR 5 128 32 "mld_invntt_blocks 3 2 (mld_invntt_layers 5 x)"
     "mld_invntt_blocks 3 3 (mld_invntt_layers 5 x)" [INV_BLOCKS_UNF 3 3];
   INV_BR 4 192 32 "mld_invntt_blocks 3 3 (mld_invntt_layers 5 x)"
     "mld_invntt_layers 6 x" [INV_LAYER_UNF 6; INV_BLOCKS_UNF 3 4];
   INV_BR 3 0 64 "mld_invntt_layers 6 x" "mld_invntt_blocks 2 1 (mld_invntt_layers 6 x)"
     [INV_BLOCKS_UNF 2 1];
   INV_BR 2 128 64 "mld_invntt_blocks 2 1 (mld_invntt_layers 6 x)" "mld_invntt_layers 7 x"
     [INV_LAYER_UNF 7; INV_BLOCKS_UNF 2 2];
   INV_BR 1 0 128 "mld_invntt_layers 7 x" "mld_invntt_layers 8 x"
     [INV_LAYER_UNF 8; INV_BLOCKS_UNF 1 1]];;

(*** The loops of layers 1 to 5 do all the blocks of the layer ***)

let INV_LAYS =
  [REWRITE_RULE[CONJUNCT1 mld_invntt_layers] (GSYM(INV_LAYER_UNF 1))] @
  map (fun n -> GSYM(INV_LAYER_UNF n)) (2--5);;

(* ------------------------------------------------------------------------- *)
(* The composition of the loops.                                             *)
(* ------------------------------------------------------------------------- *)

let INV_APPEND_CONG = prove
 (`!(a:(A)list) b c d. a = c /\ b = d ==> APPEND a b = APPEND c d`,
  MESON_TAC[]);;

let INV_EVENTS_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[APPEND_NIL; CONJUNCT1 APPEND; GSYM APPEND_ASSOC] THEN
    REPEAT(MATCH_MP_TAC INV_APPEND_CONG THEN CONJ_TAC THENL
            [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]) THEN
    FULL_UNIFY_F_EVENTS_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[APPEND_NIL; CONJUNCT1 APPEND; GSYM APPEND_ASSOC] THEN
  DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

(*** The input function of loop k ***)

let INV_INPUTS =
  [`x:num->int32`; `mld_invntt_layers 1 x`; `mld_invntt_layers 2 x`;
   `mld_invntt_layers 3 x`; `mld_invntt_layers 4 x`;
   `mld_invntt_layers 5 x`; `mld_invntt_blocks 3 1 (mld_invntt_layers 5 x)`;
   `mld_invntt_blocks 3 2 (mld_invntt_layers 5 x)`;
   `mld_invntt_blocks 3 3 (mld_invntt_layers 5 x)`;
   `mld_invntt_layers 6 x`; `mld_invntt_blocks 2 1 (mld_invntt_layers 6 x)`;
   `mld_invntt_layers 7 x`; `mld_invntt_layers 8 x`];;

(*** The instructions before loop k (from the exit of the previous loop), and the position of an adrp among them, with its constant ***)

let INV_PRE = [15; 6; 7; 6; 6; 8; 7; 7; 7; 7; 7; 6; 6];;
let INV_ADRP = [12,247592; 0,0; 2,247844; 1,247716; 2,247652; 0,0; 0,0; 0,0; 0,0; 0,0; 0,0; 0,0; 0,0];;
let INV_EPI = 27;;

let INV_FULL_TAC =
  let hname k = "H_L"^string_of_int k in
  let args = "a pc stackpointer returnaddress" in
  let template = parse_term(Printf.sprintf
   "\\(a:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      APPEND (f_ev_epi %s) %s :(uarch_event)list"
    args
    (let rec build k =
       if k = 0 then Printf.sprintf "(f_ev_pro %s)" args
       else Printf.sprintf "(APPEND (f_ev_l%d %s) %s)" k args (build (k-1)) in
     build 13)) in
  let call k s =
    FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc INV_EXEC (hname k)
     ([`a:int64`; el (k-1) INV_INPUTS; `pc:num`] @ (if k = 5 then [`stackpointer:int64`] else []))
     [`pc:num`; `a:int64`; `stackpointer:int64`; `returnaddress:int64`] (s + 1) in
  let bridge k =
    if k = 1 then RULE_ASSUM_TAC(REWRITE_RULE[el 0 INV_LAYS])
    else if k <= 5 then RULE_ASSUM_TAC(REWRITE_RULE[el (k-1) INV_LAYS])
    else if k <= 12 then RULE_ASSUM_TAC(REWRITE_RULE[el (k-6) INV_BRS])
    else ALL_TAC in
  let steps_before k t =
    let m = el (k-1) INV_PRE in
    let (p,kk) = el (k-1) INV_ADRP in
    if p > 0 then
      ARM_STEPS_TAC INV_EXEC ((t+1) -- (t+p)) THEN MLKEM_NATIVE_ADRP_TAC THEN
      ARM_STEPS_TAC INV_EXEC ((t+p+1) -- (t+m)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; mk_small_numeral kk] WORD_ADD])
    else ARM_STEPS_TAC INV_EXEC ((t+1) -- (t+m)) in
  MAP_EVERY (fun k -> ASSUME_CALLEE_SAFETY_TAILED_TAC (el (k-1) INV_LS) (hname k))
            (1 -- 13) THEN
  CONCRETIZE_F_EVENTS_TAC template THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst INV_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun k -> ENSURES_PRESERVED_TAC (Printf.sprintf "x%d_init" k) (parse_term (Printf.sprintf "X%d" k))) (19--29) THEN
  FULL_INIT_TAC THEN
  (let rec go k t =
     if k > 13 then
       ARM_STEPS_TAC INV_EXEC ((t+1) -- (t+INV_EPI)) THEN
       ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[mld_poly_invntt_tomont] THEN
       RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `247592`] WORD_ADD]) THEN
       INV_EVENTS_TAC
     else
       steps_before k t THEN
       (let t' = t + el (k-1) INV_PRE in
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

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  INV_FULL_TAC);;

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
