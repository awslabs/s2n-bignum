(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The code and read-only data of mlkem-native's libmlkem.so compiled by     *)
(* gcc 12 with -O2 (see mlkem_native/README.md), as one image, and tools to  *)
(* transfer the results for the individual functions to the same code in     *)
(* the image. All the theorems about the image assume that it is loaded at   *)
(* an address pc that is a multiple of 4096, as the dynamic loader does, and *)
(* that it does not wrap around the end of the address space, i.e.           *)
(* pc + 0x6480 <= 2 EXP 64. The functions in it are then at pc + <address>,  *)
(* where <address> is the address of the function in the binary.             *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

let mlkem_native_libmlkem_gcc12_O2_mc = define_from_elf
  "mlkem_native_libmlkem_gcc12_O2_mc"
  "arm/mlkem_native/mlkem_native_libmlkem_gcc12_O2.o";;

let LENGTH_MLKEM_NATIVE_LIBMLKEM_GCC12_O2_MC =
  CONV_RULE(RAND_CONV LENGTH_CONV)
   (AP_TERM `LENGTH:byte list->num` mlkem_native_libmlkem_gcc12_O2_mc);;

(* ------------------------------------------------------------------------- *)
(* Decoding all the code in the image would take several minutes, and the    *)
(* header and the data in it are not instructions, so the decoding theorems  *)
(* for the simulation are only made for the given ranges of addresses        *)
(* [lo,hi), which are those of the code being simulated. Otherwise this is   *)
(* the same as ARM_MK_EXEC_RULE.                                             *)
(* ------------------------------------------------------------------------- *)

let ARM_MK_EXEC_RANGES_RULE =
  let pth = (UNDISCH_ALL o prove)
   (`i = i' ==> pc + 4 = pc' ==>
     aligned_bytes_loaded s (word pc) l ==>
     read_int32 l = SOME (a, l') ==> decode a = SOME i ==>
     arm_decode s (word pc) i' /\
     aligned_bytes_loaded s (word pc') l'`,
    REPEAT (DISCH_THEN (SUBST1_TAC o SYM)) THEN
    MATCH_ACCEPT_TAC ARM_DECODE_CONS)
  and pth_pc = (UNDISCH o ARITH_RULE) `n + 4 = p ==> (pc + n) + 4 = pc + p`
  and r32,dec,n4 = `read_int32`,`decode`,`4`
  and ei,ei' = `i:armstate->armstate->bool`,`i':armstate->armstate->bool`
  and pl,el,el' = `(+):num->num->num`,`l:byte list`,`l':byte list`
  and ea,en,ep,epc,epc' = `a:int32`,`n:num`,`p:num`,`pc:num`,`pc':num`
  and len_tm = `LENGTH:byte list->num` in
  let rec go k th =
    if k <= 0 then [] else
    let pc,l = (rand o rand F_F I) (dest_comb (concl th)) in
    let th1 = READ_WORD_CONV (mk_comb (r32, l)) in
    let a,l' = dest_pair (rand (rhs (concl th1))) in
    let th2 = DECODE_CONV (mk_comb (dec, a)) in
    let i = rand (rhs (concl th2)) in
    let th3 = REWRITE_CONV (invert_condition :: ARM_INSTRUCTION_ALIASES) i in
    let i' = rhs (concl th3) in
    let th4,pcofs = match pc with
    | Comb(Comb(Const("+",_),pc),a) ->
      let th = NUM_ADD_CONV (mk_comb (mk_comb (pl, a), n4)) in
      PROVE_HYP th (INST [pc,epc; a,en; rhs (concl th),ep] pth_pc),a
    | _ -> REFL (mk_comb (mk_comb (pl, pc), n4)),`0` in
    let pc' = rhs (concl th4) in
    let th' = itlist PROVE_HYP [th3; th4; th; th1; th2]
      (INST [i,ei; i',ei'; pc,epc; pc',epc'; l,el; a,ea; l',el'] pth) in
    match l' with
    | Const("NIL",_) -> [CONJUNCT1 th',pcofs]
    | _ -> let dth,bth = CONJ_PAIR th' in (dth,pcofs)::(go (k - 1) bth) in
  fun mc_def ranges ->
    let lenth = TRANS (AP_TERM len_tm mc_def)
                      (LENGTH_CONV (mk_comb(len_tm,rhs(concl mc_def)))) in
    let dth = AP_TERM `aligned_bytes_loaded s (word pc)` mc_def in
    let th0 = EQ_MP dth (ASSUME (lhs (concl dth))) in
    let decodes = itlist (fun (lo,hi) acc ->
      go ((hi - lo) / 4) (ALIGNED_BYTES_LOADED_OFFSET_RULE lo th0) @ acc)
      ranges [] in
    let arr = Array.make (dest_small_numeral (rhs (concl lenth))) None in
    List.iter (fun (th,pcofs) ->
        arr.(dest_small_numeral pcofs) <-
          Some ((GENL [`s:armstate`; `pc:num`] o DISCH_ALL) th))
      decodes;
    lenth,arr;;

(* ------------------------------------------------------------------------- *)
(* Addresses in the image when it is at a multiple of 4096.                  *)
(* ------------------------------------------------------------------------- *)

let ALIGNED_4096_WORD_AND = prove
 (`!x:int64. aligned 4096 x <=> word_and x (word 4095) = word 0`,
  GEN_TAC THEN REWRITE_TAC[aligned; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`x:int64`; `12`] (CONJUNCT1 WORD_AND_MASK_WORD)) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIVIDES_MOD; GSYM VAL_EQ_0; VAL_WORD; DIMINDEX_64] THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `x MOD 4096 < 4096`; ARITH_RULE
    `x < 4096 ==> x < 2 EXP 64`]);;

(*** The page and the offset within it computed by ADRP and ADD or LDR ***)

let PAGE_ADD_ALIGNED = prove
 (`!x y:int64.
        word_and x (word 4095) = word 0
        ==> word_and (word_add x y) (word 0xFFFFFFFFFFFFF000) =
            word_add x (word_and y (word 0xFFFFFFFFFFFFF000)) /\
            word_subword (word_add x y) (0,12):(12)word =
            word_subword y (0,12) /\
            word_subword (word_add x y) (4,8):(12)word =
            word_subword y (4,8)`,
  BITBLAST_TAC);;

(*** The range check for ADRP holds within an image without wraparound ***)

let ADRP_WITHIN_BOUNDS_ALIGNED = prove
 (`!pc a b.
        aligned 4096 (word pc:int64) /\
        pc + a < 2 EXP 64 /\ pc + b < 2 EXP 64 /\
        a < 2 EXP 32 /\ b < 2 EXP 32
        ==> adrp_within_bounds (word (pc + b)) (word (pc + a))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[aligned; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `pc MOD 18446744073709551616 = pc` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC o REWRITE_RULE[divides]) THEN
  REWRITE_TAC[adrp_within_bounds] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[word_uge; word_ult; word_ule; relational2; VAL_WORD_SUB_CASES;
              VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  REWRITE_TAC[ARITH_RULE `(4096 * x + b) DIV 4096 = x + b DIV 4096`] THEN
  MP_TAC(SPECL [`4096`; `a:num`] DIV_MUL_LE) THEN
  MP_TAC(SPECL [`4096`; `b:num`] DIV_MUL_LE) THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(x + a DIV 4096) MOD 18014398509481984 = x + a DIV 4096 /\
                (x + b DIV 4096) MOD 18014398509481984 = x + b DIV 4096`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Given the definition of the code of a function, as it is in the image     *)
(* at address v, and the addresses d1,...,dk in the image of the data that   *)
(* the code refers to with relocations (if any), which are the extra         *)
(* arguments of the definition, give                                         *)
(*                                                                           *)
(* |- !s pc. aligned_bytes_loaded s (word pc)                                *)
(*             mlkem_native_libmlkem_gcc12_O2_mc /\                          *)
(*           aligned 4096 (word pc)                                          *)
(*           ==> aligned_bytes_loaded s (word(pc + v))                       *)
(*                 (<mc> (pc + v) (pc + d1) ... (pc + dk))                   *)
(*                                                                           *)
(* (without the alignment if there are no relocations). With the image at a  *)
(* multiple of 4096, the relocated instructions are the same as in the       *)
(* image, wherever it is.                                                    *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_IMAGE_CODE_RULE =
  let pc_tm = `pc:num` and al_tm = `aligned 4096 (word pc:int64)`
  and plus_tm = `(+):num->num->num`
  and abl_tm = mk_comb(`aligned_bytes_loaded s (word pc)`,
                       lhs(concl mlkem_native_libmlkem_gcc12_O2_mc)) in
  let pths = MATCH_MP PAGE_ADD_ALIGNED
   (UNDISCH(fst(EQ_IMP_RULE(SPEC `word pc:int64` ALIGNED_4096_WORD_AND))))
  and wsub = WORD_RULE
   `word_sub (word_add a x) (word_add a y):int64 = word_sub x y` in
  let conv =
    GEN_REWRITE_CONV ONCE_DEPTH_CONV [GSYM ADD_ASSOC] THENC
    DEPTH_CONV NUM_ADD_CONV THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV [WORD_ADD] THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV [pths; wsub] THENC
    WORD_REDUCE_CONV THENC
    REWRITE_CONV[encode_ADRP; encode_ADD_rri64; encode_LDR_Q_rri] THENC
    WORD_REDUCE_CONV THENC NUM_REDUCE_CONV in
  fun mc_def v ds ->
    let inst =
      if ds = [] then mc_def else
      let offs = map (mk_binop plus_tm pc_tm o mk_small_numeral) (v::ds) in
      CONV_RULE (RAND_CONV conv) (SPECL offs mc_def) in
    let th = UNDISCH_ALL(SPEC_ALL(ALIGNED_BYTES_LOADED_SUBPROGRAM_RULE
               mlkem_native_libmlkem_gcc12_O2_mc inst v)) in
    let th' = itlist DISCH (abl_tm::(if ds = [] then [] else [al_tm])) th in
    if hyp th' <> [] then failwith "MLKEM_NATIVE_IMAGE_CODE_RULE" else
    GENL [`s:armstate`; pc_tm] (REWRITE_RULE[IMP_IMP] th');;

(* ------------------------------------------------------------------------- *)
(* Likewise for a table of data that is at address d in the image, give      *)
(*                                                                           *)
(* |- !s pc. aligned_bytes_loaded s (word pc)                                *)
(*             mlkem_native_libmlkem_gcc12_O2_mc                             *)
(*           ==> bytes_loaded s (word(pc + d)) <data>                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_IMAGE_DATA_RULE data_def d =
  let th = ALIGNED_BYTES_LOADED_SUBPROGRAM_RULE
             mlkem_native_libmlkem_gcc12_O2_mc data_def d in
  let th' = UNDISCH(SPEC_ALL th) in
  GENL [`s:armstate`; `pc:num`]
   (DISCH_ALL(CONJUNCT2(REWRITE_RULE[aligned_bytes_loaded] th')));;

(* ------------------------------------------------------------------------- *)
(* Prove the version of a theorem for a function in the image, given the     *)
(* theorem for the function with the variables for the addresses of the      *)
(* code and of the data instantiated to pc + v and pc + d1, ..., and its     *)
(* other variables free with the same names as in the goal, and the          *)
(* theorems from the two rules above for its code and data. The hypotheses   *)
(* about the addresses of the code and data, such as the bounds for ADRP     *)
(* and alignment for LDR of a Q register, follow from those for the image.   *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_IMAGE_TAC =
  let pth = ONCE_REWRITE_RULE[IMP_CONJ_ALT] ENSURES_PRECONDITION_THM
  and ath = REWRITE_RULE[IMP_IMP] (SPECL [`16`; `4096`] ALIGNED_WORD_WEAKEN) in
  fun th loadths ->
    REWRITE_TAC[ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
    REPEAT STRIP_TAC THEN MP_TAC th THEN ANTS_TAC THENL
     [REWRITE_TAC[GSYM ADD_ASSOC; ALL; ALLPAIRS] THEN
      CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      FIRST
       [MATCH_MP_TAC ADRP_WITHIN_BOUNDS_ALIGNED THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o check
         (can (term_match [] `pc + n <= 2 EXP 64`) o concl)) THEN
        ARITH_TAC;
        REWRITE_TAC[WORD_ADD] THEN
        CONV_TAC NORMALIZE_ALIGNED_WORD_CONV THEN
        MATCH_MP_TAC ath THEN ASM_REWRITE_TAC[] THEN CONV_TAC DIVIDES_CONV;
        REWRITE_TAC[WORD_ADD] THEN NONOVERLAPPING_TAC];
      DISCH_THEN(MATCH_MP_TAC o MATCH_MP pth) THEN
      X_GEN_TAC `s:armstate` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_SIMP_TAC loadths];;

(* ------------------------------------------------------------------------- *)
(* The same for a theorem of constant time and memory safety, of the form    *)
(* |- ?f_events. !e ... . P ==> ensures arm (...) (... f_events ...) (...).  *)
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

(* ------------------------------------------------------------------------- *)
(* Vectors of polynomials. As in common/fips203.ml, a vector of k            *)
(* polynomials is given by its 256 * k coefficients, those of polynomial j   *)
(* being \i. x(256 * j + i). POLYVEC_SPLIT_TAC k splits an assumption        *)
(* !i. i < 256 * k ==> P i into one for each polynomial, POLYVEC_JOIN_TAC k  *)
(* reduces such a goal to the cases for the polynomials, and                 *)
(* POLYVEC_CASES_TAC reduces a goal !j. j < k ==> Q j to Q 0, ...,           *)
(* Q (k - 1), with the indices and offsets evaluated in each case.           *)
(* ------------------------------------------------------------------------- *)

let POLYVEC_SPLIT = prove
 (`!k j P. (!i. i < 256 * k ==> P i) /\ j < k
           ==> !i. i < 256 ==> P(256 * j + i)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  TRANS_TAC LTE_TRANS `256 * (j + 1)` THEN
  ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC);;

let POLYVEC_JOIN = prove
 (`!k P. (!j. j < k ==> !i. i < 256 ==> P(256 * j + i))
         ==> !i. i < 256 * k ==> P i`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i DIV 256`) THEN
  ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
  DISCH_THEN(MP_TAC o SPEC `i MOD 256`) THEN
  REWRITE_TAC[MOD_LT_EQ; ARITH_EQ; DIVISION_SIMP]);;

let POLYVEC_INDEX_CONV =
  TOP_DEPTH_CONV BETA_CONV THENC
  REWRITE_CONV[LEFT_ADD_DISTRIB; MULT_ASSOC] THENC NUM_REDUCE_CONV THENC
  REWRITE_CONV[ADD_CLAUSES];;

let POLYVEC_SPLIT_TAC k =
  let kt = mk_small_numeral k in
  let sth = CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) (SPEC kt POLYVEC_SPLIT) in
  let jths = map (fun j ->
    let jt = mk_small_numeral j in
    jt,EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool` jt kt)))
    (0--(k-1)) in
  let n = mk_small_numeral(256 * k) in
  FIRST_X_ASSUM(fun th ->
    let i,bod = dest_forall(concl th) in
    if rand(lhand bod) <> n then failwith "POLYVEC_SPLIT_TAC" else
    MAP_EVERY (fun (jt,jth) ->
      ASSUME_TAC(CONV_RULE POLYVEC_INDEX_CONV
        (MATCH_MP (SPEC jt sth) (CONJ th jth)))) jths);;

let POLYVEC_CASES_TAC =
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC POLYVEC_INDEX_CONV;;

let POLYVEC_JOIN_TAC k =
  let kt = mk_small_numeral k in
  MATCH_MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
                (SPEC kt POLYVEC_JOIN)) THEN
  POLYVEC_CASES_TAC;;

(* ------------------------------------------------------------------------- *)
(* Byte arrays. As in mlkem_decode in common/fips203.ml, the contents of a   *)
(* byte array are given as a number n, and READ_MEMORY_BYTES8_OF_NUM gives   *)
(* its bytes. BYTES_BITBLAST_TAC proves a goal of bit operations on such     *)
(* bytes word((n DIV 2 EXP k) MOD 256) by bit-blasting with them as atoms.   *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES8_OF_NUM = prove
 (`!a:int64 m n k s:armstate.
        read (memory :> bytes(a,m)) s = n /\ k < m
        ==> read (memory :> bytes8(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 256)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES8_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP (8 * 1)`; READ_BYTES_DIV;
              READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let BYTES_BITBLAST_TAC (asl,w) =
  let bts = setify (find_terms (fun t ->
     type_of t = `:byte` &&
     can (term_match [] `word(x MOD 256):byte`) t) w) in
  let vs = map (fun _ -> genvar `:byte`) bts in
  let th = BITBLAST_RULE (subst (zip vs bts) w) in
  ACCEPT_TAC (INST (zip bts vs) th) (asl,w);;
