(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for proofs about the code of a whole binary image (a byte list      *)
(* <image> from address 0 of the binary, e.g. up to the end of .rodata, as   *)
(* written by tools/elf_transcribe.py), loaded at an address pc that is a    *)
(* multiple of 4096, as the dynamic loader does, and not wrapping around the *)
(* end of the address space. None of them depends on the binary; the rules  *)
(* whose names end in _FOR take the definition of the image as their first  *)
(* argument. Generalized from arm/proofs/utils/mlkem_native_image.ml of the  *)
(* mlkem-native proofs. The relocated data of the writable segment is the    *)
(* business of common/elf_image.ml.                                          *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/loaded_image.ml";;

(* ------------------------------------------------------------------------- *)
(* Decoding all the code in an image takes minutes, and the header and the   *)
(* data in it are not instructions, so the decoding theorems for the         *)
(* simulation are only made for the given ranges of addresses [lo,hi),       *)
(* which are those of the code being simulated. Otherwise this is the same   *)
(* as ARM_MK_EXEC_RULE.                                                      *)
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
    let i = try rand (rhs (concl th2)) with Failure _ ->
      failwith ("ARM_MK_EXEC_RANGES_RULE: no instruction " ^
                string_of_term a ^ " at offset " ^ string_of_term pc) in
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
(* Constants in the image. IMAGE_CONST_RULE_FOR <image> d k gives            *)
(*                                                                           *)
(* |- !s pc. aligned_bytes_loaded s (word pc) <image>                        *)
(*           ==> read (memory :> bytes<k> (word_add (word pc) (word d))) s = *)
(*               word v                                                      *)
(*                                                                           *)
(* for the k-bit value v (k = 8, 16, 32, 64 or 128) at address d in the      *)
(* image. The address is in the form that the simulation gives for an        *)
(* address computed by ADRP and an offset after IMAGE_ADRP_TAC, which puts   *)
(* the page computed by ADRP in an image at a multiple of 4096 in the form   *)
(* word_add (word pc) (word p).                                              *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_WBYTES_LOADED = prove
 (`!(a:int64) (l:byte list) s:armstate.
        aligned_bytes_loaded s a l /\ LENGTH l = dimindex(:N) DIV 8
        ==> read (memory :> wbytes a) s:N word = word(num_of_bytelist l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[aligned_bytes_loaded; bytes_loaded] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o CONJUNCT2) ASSUME_TAC) THEN
  REWRITE_TAC[READ_BYTELIST_EQ_BYTES] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM WORD_VAL] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[]);;

let IMAGE_CONST_RULE_FOR image_mc =
  let rec take n l =
    if n = 0 then [] else
    match l with h::t -> h::take (n - 1) t | [] -> failwith "take" in
  let rec drop n l =
    if n = 0 then l else
    match l with _::t -> drop (n - 1) t | [] -> failwith "drop" in
  let imagel = dest_list(rhs(concl image_mc)) in
  let wbths = [8,BYTES8_WBYTES; 16,BYTES16_WBYTES; 32,BYTES32_WBYTES;
               64,BYTES64_WBYTES; 128,BYTES128_WBYTES] in
  let abl_tm = mk_comb(`aligned_bytes_loaded s (word pc)`,
                       lhs(concl image_mc)) in
  fun d k ->
    let l = mk_list(take (k / 8) (drop d imagel),`:byte`) in
    let th1 = UNDISCH(SPEC_ALL(ALIGNED_BYTES_LOADED_SUBPROGRAM_RULE
                image_mc (REFL l) d)) in
    let a = rand(rator(concl th1)) in
    let lth = ISPECL [a; l; `s:armstate`]
               (INST_TYPE [mk_finty(Num.num_of_int k),`:N`]
                          READ_MEMORY_WBYTES_LOADED) in
    let lenth = prove(rand(lhand(concl lth)),
      REWRITE_TAC[LENGTH] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV) in
    let th2 = MP lth (CONJ th1 lenth) in
    let th3 = CONV_RULE(RAND_CONV(RAND_CONV
      (REWRITE_CONV[num_of_bytelist] THENC DEPTH_CONV WORD_RED_CONV THENC
       NUM_REDUCE_CONV))) th2 in
    let th4 = REWRITE_RULE[GSYM(assoc k wbths); WORD_ADD] th3 in
    GENL [`s:armstate`; `pc:num`] (DISCH abl_tm th4);;

(* ------------------------------------------------------------------------- *)
(* IMAGE_ADRP_TAC rewrites, in the assumptions, the pages computed by ADRP   *)
(* in an image at pc, word_and (word(pc + k)) (word 0xFFFFFFFFFFFFF000),     *)
(* to word_add (word pc) (word p) for the numeral p, using the assumption    *)
(* aligned 4096 (word pc).                                                   *)
(* ------------------------------------------------------------------------- *)

let IMAGE_ADRP_TAC =
  let mask = `word 0xFFFFFFFFFFFFF000:int64` in
  let is_page t =
    match t with
      Comb(Comb(Const("word_and",_),
                Comb(Const("word",_),
                     Comb(Comb(Const("+",_),Var("pc",_)),k))),m)
        -> m = mask && is_numeral k
    | _ -> false in
  W(fun (asl,w) ->
    let ath = snd(find (fun (_,th) ->
                concl th = `aligned 4096 (word pc:int64)`) asl) in
    let pth = GEN_ALL(CONJUNCT1(SPEC_ALL(MATCH_MP PAGE_ADD_ALIGNED
                (REWRITE_RULE[ALIGNED_4096_WORD_AND] ath)))) in
    let conv t =
      if is_page t then
        (LAND_CONV(REWR_CONV WORD_ADD) THENC REWR_CONV pth THENC
         RAND_CONV WORD_REDUCE_CONV) t
      else failwith "IMAGE_ADRP_TAC" in
    let rule th =
      if can (find_term is_page) (concl th) then
        CONV_RULE(ONCE_DEPTH_CONV conv THENC
                  ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th
      else th in
    RULE_ASSUM_TAC rule);;
