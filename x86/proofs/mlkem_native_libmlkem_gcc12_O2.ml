(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The code and read-only data of mlkem-native's libmlkem.so for x86-64      *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md), as one image,   *)
(* and tools to transfer the results for the individual functions to the     *)
(* same code in the image. The code refers to other code and data in the     *)
(* image only by displacements from the instruction pointer, so the image    *)
(* works in the same way wherever it is loaded, at an address pc, and the    *)
(* functions in it are then at pc + <address>, where <address> is the        *)
(* address of the function in the binary. The theorems about the image only  *)
(* assume that pc is a multiple of 16, since the vectors of constants read   *)
(* by SSE instructions must be aligned. (The dynamic loader puts it at a     *)
(* multiple of 4096.)                                                        *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

let mlkem_native_libmlkem_gcc12_O2_mc = define_from_elf
  "mlkem_native_libmlkem_gcc12_O2_mc"
  "x86/mlkem_native/mlkem_native_libmlkem_gcc12_O2.o";;

let LENGTH_MLKEM_NATIVE_LIBMLKEM_GCC12_O2_MC =
  CONV_RULE(RAND_CONV LENGTH_CONV)
   (AP_TERM `LENGTH:byte list->num` mlkem_native_libmlkem_gcc12_O2_mc);;

(* ------------------------------------------------------------------------- *)
(* Decoding all the code in the image would take several minutes, and the    *)
(* header and the data in it are not instructions, so the decoding theorems  *)
(* for the simulation are only made for the given ranges of addresses        *)
(* [lo,hi), which are those of the code being simulated. Otherwise this is   *)
(* the same as X86_MK_EXEC_RULE.                                             *)
(* ------------------------------------------------------------------------- *)

let X86_MK_EXEC_RANGES_RULE =
  let pth = (UNDISCH_ALL o prove)
   (`i = i' ==> pc + n = pc' ==>
     bytes_loaded s (word pc) l ==> decode_len l (n,i) l' ==>
     x86_decode s (word pc) (n,i') /\ bytes_loaded s (word pc') l'`,
    REPEAT (DISCH_THEN (SUBST1_TAC o SYM)) THEN
    MATCH_ACCEPT_TAC X86_DECODE_CONS)
  and pth_pc = (UNDISCH o ARITH_RULE) `n + m:num = p ==> (pc + n) + m = pc + p`
  and ei,ei' = `i:instruction`,`i':instruction`
  and pl,el,el' = `(+):num->num->num`,`l:byte list`,`l':byte list`
  and en,em,ep,epc,epc' = `n:num`,`m:num`,`p:num`,`pc:num`,`pc':num`
  and len_tm = `LENGTH:byte list->num` in
  let offset_of pc = match pc with
    | Comb(Comb(Const("+",_),_),a) -> dest_small_numeral a
    | _ -> 0 in
  let rec go hi th =
    let l = rand (concl th) in
    let th1 = DECODE_LEN_THM l in
    let (n,i),l' = (dest_pair o rand F_F I) (dest_comb (concl th1)) in
    let th2 = REWRITE_CONV X86_INSTRUCTION_ALIASES i in
    let i' = rhs (concl th2) in
    let pc = rand (lhand (concl th)) in
    let th3,pcofs = match pc with
    | Comb(Comb(Const("+",_),pc),a) ->
      let th = NUM_ADD_CONV (mk_comb (mk_comb (pl, a), n)) in
      PROVE_HYP th (INST [pc,epc; a,en; n,em; rhs (concl th),ep] pth_pc),a
    | _ -> REFL (mk_comb (mk_comb (pl, pc), n)),`0` in
    let pc' = rhs (concl th3) in
    let th' = (PROVE_HYP th2 o PROVE_HYP th3 o PROVE_HYP th o PROVE_HYP th1)
      (INST [i,ei; i',ei'; pc,epc; n,en; pc',epc'; l,el; l',el'] pth) in
    let dth,bth = CONJ_PAIR th' in
    if offset_of pc' >= hi then [dth,pcofs]
    else (dth,pcofs)::(go hi bth) in
  fun mc_def ranges ->
    let lenth = TRANS (AP_TERM len_tm mc_def)
                      (LENGTH_CONV (mk_comb(len_tm,rhs(concl mc_def)))) in
    let dth = AP_TERM `bytes_loaded s (word pc)` mc_def in
    let th0 = EQ_MP dth (ASSUME (lhs (concl dth))) in
    let decodes = itlist (fun (lo,hi) acc ->
      go hi (BYTES_LOADED_OFFSET_RULE lo th0) @ acc) ranges [] in
    let arr = Array.make (dest_small_numeral (rhs (concl lenth))) None in
    List.iter (fun (th,pcofs) ->
        arr.(dest_small_numeral pcofs) <-
          Some ((GENL [`s:x86state`; `pc:num`] o DISCH_ALL) th))
      decodes;
    lenth,arr;;

(* ------------------------------------------------------------------------- *)
(* Addresses in the image: a RIP-relative displacement from code in the      *)
(* image to data in it is within range wherever the image is.                *)
(* ------------------------------------------------------------------------- *)

let RIPREL32_WITHIN_BOUNDS_IN_IMAGE = prove
 (`!pc a b. a < 2 EXP 31 /\ b < 2 EXP 31
            ==> riprel32_within_bounds (pc + a) (pc + b)`,
  REWRITE_TAC[riprel32_within_bounds; GSYM INT_OF_NUM_ADD] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_POW] THEN INT_ARITH_TAC);;

let IMAGE_INT_SUB_LEMMA = prove
 (`!p a b c. &(p + a) - (&(p + b) + c):int = &a - (&b + c)`,
  REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Given the definition of the code of a function, as it is in the image     *)
(* at address v, and the addresses d1,...,dk in the image of the data that   *)
(* the code refers to with relocations (if any), which are the extra         *)
(* arguments of the definition, give                                         *)
(*                                                                           *)
(* |- !s pc. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc      *)
(*           ==> bytes_loaded s (word(pc + v))                               *)
(*                 (<mc> (pc + v) (pc + d1) ... (pc + dk))                   *)
(*                                                                           *)
(* The relocated displacements are then constants, the same as in the image, *)
(* wherever it is.                                                           *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_IMAGE_CODE_RULE =
  let pc_tm = `pc:num` and plus_tm = `(+):num->num->num` in
  let conv =
    GEN_REWRITE_CONV TOP_DEPTH_CONV [IMAGE_INT_SUB_LEMMA] THENC
    NUM_REDUCE_CONV THENC INT_REDUCE_CONV THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV [NUM_OF_INT_OF_NUM] THENC
    NUM_REDUCE_CONV in
  fun mc_def v ds ->
    let inst =
      if ds = [] then mc_def else
      let offs = map (mk_binop plus_tm pc_tm o mk_small_numeral) (v::ds) in
      CONV_RULE (RAND_CONV conv) (SPECL offs mc_def) in
    BYTES_LOADED_SUBPROGRAM_RULE mlkem_native_libmlkem_gcc12_O2_mc inst v;;

(* ------------------------------------------------------------------------- *)
(* Likewise for a table of data that is at address d in the image, give      *)
(*                                                                           *)
(* |- !s pc. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc      *)
(*           ==> bytes_loaded s (word(pc + d)) <data>                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_IMAGE_DATA_RULE data_def d =
  BYTES_LOADED_SUBPROGRAM_RULE mlkem_native_libmlkem_gcc12_O2_mc data_def d;;

(* ------------------------------------------------------------------------- *)
(* Prove the version of a theorem for a function in the image, given the     *)
(* theorem for the function with the variables for the addresses of the      *)
(* code and of the data instantiated to pc + v and pc + d1, ..., and its     *)
(* other variables free with the same names as in the goal, and the          *)
(* theorems from the two rules above for its code and data. The hypotheses   *)
(* about the addresses of the code and data, such as the bounds for the      *)
(* RIP-relative displacements and the alignment of vectors of constants,     *)
(* follow from those for the image.                                          *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_IMAGE_TAC =
  let pth = ONCE_REWRITE_RULE[IMP_CONJ_ALT] ENSURES_PRECONDITION_THM in
  fun th loadths ->
    REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN
    REPEAT STRIP_TAC THEN MP_TAC th THEN ANTS_TAC THENL
     [REWRITE_TAC[GSYM ADD_ASSOC; ALL] THEN
      CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      FIRST
       [MATCH_MP_TAC RIPREL32_WITHIN_BOUNDS_IN_IMAGE THEN
        CONV_TAC NUM_REDUCE_CONV;
        REWRITE_TAC[WORD_ADD] THEN
        CONV_TAC NORMALIZE_ALIGNED_WORD_CONV THEN FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC[WORD_ADD] THEN NONOVERLAPPING_TAC];
      DISCH_THEN(MATCH_MP_TAC o MATCH_MP pth) THEN
      X_GEN_TAC `s:x86state` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_SIMP_TAC loadths];;

(* ------------------------------------------------------------------------- *)
(* The same for a theorem of constant time and memory safety, of the form    *)
(* |- ?f_events. !e ... . P ==> ensures x86 (...) (... f_events ...) (...). *)
(* The function of the events in the image is that of the function with the  *)
(* instantiations, as a function of the arguments of f_events in the goal.   *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_IMAGE_SAFE_TAC th inst loadths =
  let f = fst(dest_exists(concl th)) in
  let app v tm = find_term (fun t -> fst(strip_comb t) = v) tm in
  X_CHOOSE_THEN f (fun fth ->
    let fth' = INST inst (SPEC_ALL fth) in
    W(fun (asl,w) ->
      let f',wbod = dest_exists w in
      let xs = snd(strip_comb(app f' wbod)) in
      let zs = map (genvar o type_of) xs in
      let wit = list_mk_abs(zs,subst (zip zs xs) (app f (concl fth'))) in
      EXISTS_TAC wit THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      MLKEM_NATIVE_IMAGE_TAC fth' loadths)) th;;
