(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/clang17_O2/poly_rej_uniform_x4_spec.ml";;
needs "arm/proofs/subroutine_signatures.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;


let MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_LOOPS_FULL =
  map REJ_LOOP_FULL MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_LOOPS;;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_LOOPS_CORRECT =
  map2 REJ_LOOP_CORRECT MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_LOOPS
   MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_LOOPS_FULL;;

(* ------------------------------------------------------------------------- *)
(* Tactics for the proofs. The stack pointer is rounded down to a multiple   *)
(* of 32 in the code, so the buffers are 352 or 336 bytes above the bottom   *)
(* of the frame, and the proofs split on the alignment of the stack pointer  *)
(* so that all the addresses are numerals; the template for the events has   *)
(* a copy for each of the two cases. The statements are those of the loops   *)
(* above and of the callees.                                                  *)
(* ------------------------------------------------------------------------- *)


let REJX4_BUFFER_ADDRESS_STMT =
  `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 352)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 352 else 336))`;;
let REJX4_BUFFER_ADDRESS = prove
 (REJX4_BUFFER_ADDRESS_STMT,
  REWRITE_TAC[REJ_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

(*** The offset of the buffers from the bottom of the frame, 352 or 336 ***)

let rejx4_b = ref 352;;

let REJX4_SP n =
  mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
          mk_comb(`word:num->int64`,mk_small_numeral(!rejx4_b + n)));;

let REJX4_ST m = REJX4_SP(64 + 200 * m);;
let REJX4_BUF m = REJX4_SP(864 + 512 * m);;

let REJX4_BUFFER_TAC g =
  let b = mk_small_numeral !rejx4_b in
  (SUBGOAL_THEN
   (subst [b,`b:num`]
    `word_and (word_add stackpointer (word 352))
              (word 18446744073709551584):int64 =
     word_add stackpointer (word b)`)
   SUBST_ALL_TAC THENL
   [MP_TAC(MATCH_MP REJX4_BUFFER_ADDRESS
             (ASSUME `aligned 16 (stackpointer:int64)`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC]) g;;

let REJX4_NORMALIZE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th
    else th);;

let REJX4_SETUP_TAC g =
  let b = mk_small_numeral !rejx4_b in
  (SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 3392):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   (subst [b,`b:num`] `aligned 16 (word_add (stackpointer:int64) (word b))`)
  ASSUME_TAC THENL
   [CONV_TAC NORMALIZE_ALIGNED_WORD_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    let r = "X"^string_of_int n in
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const(r,[]))) (19--29)) g;;

let REJX4_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`vec0:int64`; `vec1:int64`; `vec2:int64`; `vec3:int64`; `seed:int64`;
    `inp0:byte list`; `inp1:byte list`; `inp2:byte list`; `inp3:byte list`;
    `k:num`; `guard:int64`; `mf:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 3392 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              GSYM REJ_SAMPLE] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> ASSUME_TAC th THEN
              LABEL_TAC "H_MEMSET" (REWRITE_RULE[memset_contract] th))
   (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC));;

(*** The proof is done separately in the two cases for the alignment of ***)
(*** the stack pointer, with numerals for the addresses                 ***)

let REJX4_CASES_TAC tac =
  ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [(fun g -> rejx4_b := 352; tac g); (fun g -> rejx4_b := 336; tac g)];;

let REJX4_SAMPLE_SUC_STMT =
  `!(f:num->byte) j.
        SUB_LIST(0,256)
         (REJ_SAMPLE(wordlist_of_num (336 + 112 * (j + 1))
            (num_of_bytelist(list_of_seq f (504 + 168 * (j + 1)))))) =
        APPEND
         (SUB_LIST(0,256)
           (REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
              (num_of_bytelist(list_of_seq f (504 + 168 * j))))))
         (SUB_LIST(0,256 -
                   MIN 256 (LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
                     (num_of_bytelist(list_of_seq f (504 + 168 * j)))))))
           (REJ_SAMPLE(wordlist_of_num 112
              (num_of_bytelist
                (list_of_seq (\i. f((504 + 168 * j) + i)) 168)))))`;;

let REJX4_SAMPLE_SUC = prove
 (REJX4_SAMPLE_SUC_STMT,
  REPEAT GEN_TAC THEN REWRITE_TAC[REJ_FIELDS_SUC; REJ_SAMPLE_APPEND] THEN
  MAP_EVERY (fun (t,v) -> SPEC_TAC(t,v))
   [`REJ_SAMPLE(wordlist_of_num 112 (num_of_bytelist
      (list_of_seq (\i. (f:num->byte)((504 + 168 * j) + i)) 168)))`,
    `l2:int16 list`;
    `REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
      (num_of_bytelist(list_of_seq (f:num->byte) (504 + 168 * j))))`,
    `l1:int16 list`] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `LENGTH(l1:int16 list) <= 256` THENL
   [ASM_SIMP_TAC[SUB_LIST_APPEND_RIGHT; SUB_LIST_REFL;
                 ARITH_RULE `x <= 256 ==> MIN 256 x = x`];
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
    ASM_SIMP_TAC[SUB_LIST_APPEND_LEFT; LT_IMP_LE; SUB_REFL;
                 ARITH_RULE `256 < x ==> MIN 256 x = 256`] THEN
    REWRITE_TAC[SUB_LIST_CLAUSES; APPEND_NIL]]);;

(*** The fields, samples and blocks for each seed ***)

let REJX4_INPS =
  [`inp0:byte list`; `inp1:byte list`; `inp2:byte list`; `inp3:byte list`]
and REJX4_VECS = [`vec0:int64`; `vec1:int64`; `vec2:int64`; `vec3:int64`]
and REJX4_SVS =
  [`S0:1600 word`; `S1:1600 word`; `S2:1600 word`; `S3:1600 word`]
and REJX4_CTRS = [`X26`; `X27`; `X28`; `X23`]
and REJX4_OUTS = [`X22`; `X21`; `X20`; `X19`];;

let rejx4_fields inp j =
  vsubst [inp,`inp:byte list`; j,`j:num`]
   `wordlist_of_num (336 + 112 * j)
     (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * j))):
    (12 word)list`;;

let rejx4_fields0 inp =
  vsubst [inp,`inp:byte list`]
   `wordlist_of_num 336
     (num_of_bytelist(list_of_seq (shake128 inp) 504)):(12 word)list`;;

let rejx4_count inp j =
  mk_comb(`LENGTH:(16 word)list->num`,
          mk_comb(`REJ_SAMPLE`,rejx4_fields inp j));;

let rejx4_count0 inp =
  rhs(concl(REWRITE_CONV[MULT_CLAUSES; ADD_CLAUSES] (rejx4_count inp `0`)));;

let rejx4_block inp i =
  vsubst [inp,`inp:byte list`; i,`i:num`]
   `wordlist_of_num 112
     (num_of_bytelist
       (list_of_seq (\j. shake128 inp ((504 + 168 * i) + j)) 168)):
    (12 word)list`;;

let rejx4_done m j =
  mk_binop `(<=):num->num->bool` `256` (rejx4_count (el m REJX4_INPS) j);;

let rejx4_done0 m =
  mk_binop `(<=):num->num->bool` `256` (rejx4_count0 (el m REJX4_INPS));;

(*** The absorbed states as S0, ..., S3, and the minimal number of blocks ***)

let REJX4_ABSORBED_TAC =
  MAP_EVERY (fun (inp,sv) ->
    let t = vsubst [inp,`inp:byte list`] REJ_ABSORBED in
    let len = ASSUME(mk_eq(mk_comb(`LENGTH:byte list->num`,inp),`34`)) in
    ABBREV_TAC(mk_eq(sv,t)) THEN
    ASSUME_TAC(REWRITE_RULE[len; ASSUME(mk_eq(t,sv))]
                (SPEC inp REJ_SPONGE)) THEN
    ASSUME_TAC(REWRITE_RULE[len; ASSUME(mk_eq(t,sv))]
                (SPEC inp REJ_SHAKE128_BLOCKS)))
   (zip REJX4_INPS REJX4_SVS);;

let REJX4_DONE n =
  list_mk_conj
   (map (fun inp -> mk_binop `(<=):num->num->bool` `256` (rejx4_count inp n))
        REJX4_INPS);;

let REJX4_MINIMAL_TAC =
  let p = mk_abs(`n:num`,REJX4_DONE `n:num`) in
  MP_TAC(BETA_RULE(fst(EQ_IMP_RULE(ISPEC p MINIMAL)))) THEN
  ANTS_TAC THENL [EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC(mk_eq(`k0:num`,mk_comb(`(minimal):(num->bool)->num`,p))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `k0 <= k` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(*** The minimality of k0, at j, without rewriting with it, which turns ***)
(*** its own instances into T                                           ***)

let REJX4_MINIMALITY_TAC j =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Const("!",_),Abs(v,Comb(Comb(Const("==>",_),
        Comb(Comb(Const("<",_),v'),Var("k0",_))),_))) when v' = v ->
        MP_TAC(SPEC j th)
    | _ -> NO_TAC);;

let REJX4_ADDRESS_TAC =
  TRY(REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC] THEN
      CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[] THEN NO_TAC);;

let REJX4_SIM_TAC th ilist n =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,th) ilist n THEN
  REJX4_ADDRESS_TAC;;

let LOCAL_INIT_X4_TAC =
  REJX4_SIM_TAC MLKEM_NATIVE_SHAKE128X4_INIT_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT;;
let LOCAL_ABSORB_X4_TAC =
  REJX4_SIM_TAC
   MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT;;
let LOCAL_SQUEEZE_X4_TAC =
  REJX4_SIM_TAC
   MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT;;
let LOCAL_RELEASE_X4_TAC =
  REJX4_SIM_TAC
   MLKEM_NATIVE_SHAKE128X4_RELEASE_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT;;

let REJX4_GOT_TAC =
  MAP_EVERY (fun n ->
    FIRST_ASSUM(fun th ->
      if can (term_match []
               (vsubst [mk_small_numeral n,`n:num`]
                 `read (memory :> bytes64
                         (word_add (word (pc:num)) (word n):int64)) s =
                  (g:int64)`)) (concl th)
      then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] th) else NO_TAC))
   [layout "got_stack_chk_guard"; layout "got_memset"];;

let REJX4_FRAME () =
 vsubst [REJX4_SP 0,`spr:int64`; REJX4_SP 2936,`can_addr:int64`]
 `read SP s = spr /\
  read X29 s = word_add stackpointer (word 3296) /\
  read (memory :> bytes64 (word_add stackpointer (word 3296))) s = x29_init /\
  read (memory :> bytes64 (word_add stackpointer (word 3304))) s =
  returnaddress /\
  read (memory :> bytes64 (word_add stackpointer (word 3312))) s = x28_init /\
  read (memory :> bytes64 (word_add stackpointer (word 3320))) s = x27_init /\
  read (memory :> bytes64 (word_add stackpointer (word 3328))) s = x26_init /\
  read (memory :> bytes64 (word_add stackpointer (word 3336))) s = x25_init /\
  read (memory :> bytes64 (word_add stackpointer (word 3344))) s = x24_init /\
  read (memory :> bytes64 (word_add stackpointer (word 3352))) s = x23_init /\
  read (memory :> bytes64 (word_add stackpointer (word 3360))) s = x22_init /\
  read (memory :> bytes64 (word_add stackpointer (word 3368))) s = x21_init /\
  read (memory :> bytes64 (word_add stackpointer (word 3376))) s = x20_init /\
  read (memory :> bytes64 (word_add stackpointer (word 3384))) s = x19_init /\
  read (memory :> bytes64 can_addr) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard))) s =
  guard /\
  read (memory :> bytes64 guard) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word got_memset))) s = mf /\
  read (memory :> bytes(ea,el)) s = ev`;;

let REJX4_POLY =
 `read (R:(armstate,int64)component) s =
  word(MIN 256 (LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * i)
    (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * i))))))) /\
  read (memory :> bytes(vec,2 * MIN 256 (LENGTH(REJ_SAMPLE
    (wordlist_of_num (336 + 112 * i)
      (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * i)))))))) s =
  num_of_wordlist(SUB_LIST(0,256) (REJ_SAMPLE(wordlist_of_num
    (336 + 112 * i)
    (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * i)))))) /\
  read (memory :> bytes(st,200)) s =
  val(keccak_squeeze (3 + i) (S:1600 word))`;;

let REJX4_POLYS regs ms =
  flat
   (map (fun m ->
          let r = el m regs and vec = el m REJX4_VECS
          and inp = el m REJX4_INPS and st = REJX4_ST m
          and sv = el m REJX4_SVS in
          conjuncts
           (vsubst [r,`R:(armstate,int64)component`; vec,`vec:int64`;
                    inp,`inp:byte list`; st,`st:int64`; sv,`S:1600 word`]
                   REJX4_POLY)) ms);;

let REJX4_AT0 t =
  rhs(concl(REWRITE_CONV[MULT_CLAUSES; ADD_CLAUSES] (vsubst [`0`,`i:num`] t)));;

(*** The flag registers, 1 if the polynomial has fewer than 256 samples ***)

let REJX4_FLAGREGS = [`X16`; `X15`; `X14`; `X25`];;

let REJX4_FLAG =
 `read (R:(armstate,int64)component) s =
  (if MIN 256 (LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * i)
    (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * i)))))) < 256
   then word 1 else word 0)`;;

let REJX4_FLAGS ms =
  map (fun m ->
    vsubst [el m REJX4_FLAGREGS,`R:(armstate,int64)component`;
            el m REJX4_INPS,`inp:byte list`] REJX4_FLAG) ms;;

let REJX4_CTRS_AT_0 () =
  REJX4_AT0 (list_mk_conj(REJX4_POLYS REJX4_CTRS [0;1;2;3]));;

let REJX4_SLOT n v =
  vsubst [REJX4_SP n,`a:int64`; v,`v:int64`]
   `read (memory :> bytes64 a) s = v`;;

let REJX4_SLOTS () =
  list_mk_conj
   [REJX4_SLOT 16 `vec0:int64`; REJX4_SLOT 24 `vec1:int64`;
    REJX4_SLOT 32 (REJX4_BUF 3); REJX4_SLOT 40 (REJX4_BUF 2);
    REJX4_SLOT 48 (REJX4_BUF 1)];;

(*** The slots written before loop4_exit ***)

let REJX4_SLOTS3 () =
  list_mk_conj
   [REJX4_SLOT 32 (REJX4_BUF 3); REJX4_SLOT 40 (REJX4_BUF 2);
    REJX4_SLOT 48 (REJX4_BUF 1)];;

(*** At loop4_exit, after the samples from the first three blocks ***)

let REJX4_A3 () =
  mk_abs(`s:armstate`,
    list_mk_conj
     (conjuncts (REJX4_CTRS_AT_0 ()) @
      map REJX4_AT0 (REJX4_FLAGS [0;1;2;3]) @
      [`read X22 s = vec0`; `read X21 s = vec1`; `read X20 s = vec2`;
       `read X19 s = vec3`] @
      conjuncts (REJX4_SLOTS3 ()) @
      conjuncts (REJX4_FRAME ())));;

(*** The fields of the first three blocks of each, before its loop ***)

let REJX4_INPUT0_TAC m s =
  let inp = el m REJX4_INPS in
  SUBGOAL_THEN
   (mk_eq(list_mk_comb(`wordlist_from_memory:int64#num->armstate->
                         (12 word)list`,
                       [mk_pair(REJX4_BUF m,`336`); s]),
          rejx4_fields0 inp))
  ASSUME_TAC THENL
   [MATCH_MP_TAC REJ_WORDLIST_FROM_BYTES THEN EXISTS_TAC `504` THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `504 = 168 * 3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let REJX4_LENGTH0_TAC m =
  ASSUME_TAC(INST_TYPE [`:12`,`:N`]
   (ISPECL [`336`; rand(rejx4_fields0 (el m REJX4_INPS))]
    LENGTH_WORDLIST_OF_NUM));;

let REJX4_LOOP_CORRECT k =
  el (if k <= 4 then k - 1 else k - 2)
     MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_LOOPS_CORRECT;;

let REJX4_LOOP_DATA k =
  el (if k <= 4 then k - 1 else k - 2)
     MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_LOOPS;;

let REJX4_LOOP_CALL k ilist n =
  REJX4_SIM_TAC (REJX4_LOOP_CORRECT k) ilist n;;

let rejx4_read r =
  list_mk_comb(`read:(armstate,int64)component->armstate->int64`,
               [mk_const(r,[]); `s:armstate`]);;

(*** The call of the copy of the loop on the first three blocks of ***)
(*** polynomial m                                                  ***)

let REJX4_LOOP0_GEN_TAC call m n =
  let inp = el m REJX4_INPS in
  let l = REJX4_LOOP_DATA (m + 1) in
  REJX4_LENGTH0_TAC m THEN
  call (m + 1)
   [list_mk_comb(`read:(armstate,int64)component->armstate->int64`,
            [el m REJX4_OUTS; `s:armstate`]); `0`; rejx4_read l.rej_base;
    `504`; rejx4_fields0 inp; `pc:num`] n THEN
  REJ_POST_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; MULT_CLAUSES; SUB_0; WORD_ADD_0;
                              LENGTH_SUB_LIST]) THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP REJ_BYTES16_OF_WORDLIST o check
   (can (term_match [] `wordlist_from_memory(a,n) s = l:int16 list`) o
    concl));;

let REJX4_LOOP0_TAC = REJX4_LOOP0_GEN_TAC REJX4_LOOP_CALL;;

(*** At the header of loop5, after 3 + i blocks of each ***)

let REJX4_INV () =
  list_mk_abs([`i:num`; `s:armstate`],
    list_mk_conj(REJX4_POLYS REJX4_CTRS (0--3) @
                 REJX4_FLAGS (0--3) @
                 [mk_eq(`read X24 s`,REJX4_BUF 0);
                  `read X19 s = vec3`; `read X20 s = vec2`] @
                 conjuncts(REJX4_SLOTS()) @
                 conjuncts(REJX4_FRAME())));;

(*** At the exit of loop5, with all the samples ***)

let REJX4_A2 () =
  let res inp vec =
    vsubst [inp,`inp:byte list`; vec,`vec:int64`]
     `read (memory :> bytes(vec,512)) s =
      num_of_wordlist(SUB_LIST(0,256) (REJ_SAMPLE(wordlist_of_num
        (336 + 112 * k)
        (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * k))))))` in
  mk_abs(`s:armstate`,
    list_mk_conj(map2 res REJX4_INPS REJX4_VECS @ conjuncts(REJX4_FRAME())));;

let REJX4_STEP_TAC n =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_EXEC [n] THEN
  REJ_NORM_TAC THEN REJ_FLAGS_TAC THEN TRY DECIDE_BRANCH_TAC;;

let rejx4_label s = rej_target ("mlkem_poly_rej_uniform_x4_" ^ s);;

let current_state_num (asl,w) =
  let s = fst(dest_var(rand w)) in
  int_of_string(String.sub s 1 (String.length s - 1));;

(*** Step until the PC is one of the targets, deciding the branches ***)

let rec REJX4_RUN_TAC targets (asl,w) =
  let p = current_pc (asl,w) in
  if mem p targets then ALL_TAC (asl,w) else
  if find_terms is_cond p <> [] then
    failwith "REJX4_RUN_TAC: undecided branch" else
  (REJX4_STEP_TAC (current_state_num (asl,w) + 1) THEN
   REJX4_RUN_TAC targets) (asl,w);;

(*** If no more block is needed, to the exit of loop5 ***)

let REJX4_NOLOOP_TAC g =
  (FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES; ADD_CLAUSES]) THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun inp ->
    let c = mk_comb(`MIN 256`,rejx4_count0 inp) in
    SUBGOAL_THEN (mk_eq(c,`256`))
     (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[ARITH_RULE `MIN a b = a <=> a <= b`] THEN ASM_REWRITE_TAC[];
      ALL_TAC]) REJX4_INPS THEN
  REJX4_RUN_TAC [rejx4_label "loop5_exit"] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun inp ->
    MP_TAC(ISPECL [mk_comb(`shake128`,inp); `0`; `k:num`]
                  REJ_SAMPLE_FINAL) THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LE_0] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC]) REJX4_INPS THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  ASM_REWRITE_TAC[]) g;;

let REJX4_ENTER_RUN_TAC =
  REJX4_RUN_TAC [rejx4_label "loop5"] THEN
  REJX4_NORMALIZE_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[];;

(*** The polynomial m has 256 samples after the first three blocks, or  ***)
(*** fewer, with its number of samples (at most 256) in the registers   ***)

let REJX4_DONE0_FACT m =
  let c = rejx4_count0 (el m REJX4_INPS) in
  fun (asl,w) ->
   (SUBGOAL_THEN (mk_eq(mk_comb(`MIN 256`,c),`256`))
     (fun th -> REJ_READ_RULE_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THENL
     [REWRITE_TAC[ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC]) (asl,w);;

let REJX4_TODO0_FACT m =
  let c = rejx4_count0 (el m REJX4_INPS) in
  SUBGOAL_THEN (mk_binop `(<):num->num->bool` c `256`) ASSUME_TAC THENL
   [FIRST_ASSUM(fun th ->
      if concl th = mk_neg(rejx4_done0 m) then MP_TAC th else NO_TAC) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REJ_MIN_FACT_TAC c;;

(*** If more blocks are needed, from loop4_exit to the header of loop5 ***)

let REJX4_ENTER_TAC =
  SUBGOAL_THEN (mk_neg(rhs(concl(REWRITE_CONV[MULT_CLAUSES; ADD_CLAUSES]
                                  (REJX4_DONE `0`)))))
   ASSUME_TAC THENL
   [REJX4_MINIMALITY_TAC `0` THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `~(k0 = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  ASM_CASES_TAC (rejx4_done0 0) THENL
   [REJX4_DONE0_FACT 0 THEN
    ASM_CASES_TAC (rejx4_done0 1) THENL
     [REJX4_DONE0_FACT 1 THEN
      ASM_CASES_TAC (rejx4_done0 2) THENL
       [REJX4_DONE0_FACT 2 THEN
         SUBGOAL_THEN (mk_neg(rejx4_done0 3)) ASSUME_TAC THENL
          [FIRST_ASSUM(fun th ->
             if is_neg(concl th) && is_conj(dest_neg(concl th))
             then MP_TAC th else NO_TAC) THEN
           REWRITE_TAC(map (fun m -> ASSUME(rejx4_done0 m)) [0;1;2]);
           ALL_TAC] THEN
         REJX4_TODO0_FACT 3 THEN REJX4_ENTER_RUN_TAC;
        REJX4_TODO0_FACT 2 THEN REJX4_ENTER_RUN_TAC];
      REJX4_TODO0_FACT 1 THEN REJX4_ENTER_RUN_TAC];
    REJX4_TODO0_FACT 0 THEN REJX4_ENTER_RUN_TAC];;

(*** The numbers of samples so far in the loop body as ci0, ..., ci3, and ***)
(*** their definitions packed into a conjunction, which keeps them from   ***)
(*** the arithmetic of NONOVERLAPPING_TAC, much slower with them          ***)

let REJX4_IS_ABBREV tm =
  match tm with
    Comb(Comb(Const("=",_),Comb(Comb(Const("MIN",_),_),_)),Var(n,_)) ->
      String.length n = 3 && String.sub n 0 2 = "ci"
  | _ -> false;;

let REJX4_ABBREV_TAC =
  MAP_EVERY (fun m ->
    let t = mk_comb(`MIN 256`,rejx4_count (el m REJX4_INPS) `i:num`) in
    ASSUME_TAC(SPECL [`256`; rand t] (ARITH_RULE `!a b. MIN a b <= a`)) THEN
    ABBREV_TAC(mk_eq(mk_var("ci"^string_of_int m,`:num`),t))) (0--3) THEN
  (fun (asl,w) ->
    let hs,ks = partition (fun (_,th) -> REJX4_IS_ABBREV(concl th)) asl in
    let cth = end_itlist CONJ (map snd hs) in
    (null_meta,[("",ASSUME(concl cth))::ks,w],
     fun i ths -> PROVE_HYP (INSTANTIATE_ALL i cth) (hd ths)));;

let REJX4_ABBREV m =
  let eq = mk_eq(mk_comb(`MIN 256`,rejx4_count (el m REJX4_INPS) `i:num`),
                 mk_var("ci"^string_of_int m,`:num`)) in
  fun (asl,w) ->
    tryfind (fun (_,th) -> find (fun th' -> concl th' = eq) (CONJUNCTS th))
            asl;;

(*** A copy of the loop on one more block, and its results ***)

let REJX4_BLOCK_TAC m s =
  let inp = el m REJX4_INPS in
  SUBGOAL_THEN
   (mk_eq(list_mk_comb(`wordlist_from_memory:int64#num->armstate->
                         (12 word)list`,
                       [mk_pair(REJX4_BUF m,`112`); s]),
          rejx4_block inp `i:num`))
  ASSUME_TAC THENL
   [MATCH_MP_TAC REJ_WORDLIST_FROM_BYTES THEN EXISTS_TAC `168` THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th ->
      if can (term_match [] `!k n. n <= 168 ==> a = b`) (concl th) &&
         free_in inp (concl th)
      then MP_TAC(SPECL [`3 + i`; `168`] th) else NO_TAC) THEN
    REWRITE_TAC[LE_REFL; ARITH_RULE `168 * (3 + i) = 504 + 168 * i`;
                ARITH_RULE `(3 + i) + 1 = 3 + i + 1`] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASSUME_TAC(INST_TYPE [`:12`,`:N`]
   (ISPECL [`112`; rand(rejx4_block inp `i:num`)] LENGTH_WORDLIST_OF_NUM));;

let REJX4_COMBINE_TAC m s =
  let inp = el m REJX4_INPS and vec = el m REJX4_VECS in
  let c = mk_var("ci"^string_of_int m,`:num`) in
  let l1 = mk_comb(`SUB_LIST(0,256):(16 word)list->(16 word)list`,
                   mk_comb(`REJ_SAMPLE`,rejx4_fields inp `i:num`))
  and l2 = mk_comb(mk_comb(`SUB_LIST:num#num->(16 word)list->(16 word)list`,
                           mk_pair(`0`,mk_binop `(-):num->num->num` `256` c)),
                   mk_comb(`REJ_SAMPLE`,rejx4_block inp `i:num`)) in
  let lenl1 = mk_eq(mk_comb(`LENGTH:(16 word)list->num`,l1),c) in
  REJ_POST_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP REJ_BYTES16_OF_WORDLIST o check
   (can (term_match [] `wordlist_from_memory(a,n) s = l:int16 list`) o
    concl)) THEN
  SUBGOAL_THEN lenl1 ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST; SUB_0] THEN
    W(fun gl -> REWRITE_TAC[REJX4_ABBREV m gl]); ALL_TAC] THEN
  MP_TAC(ISPECL [vec; c; l1; l2; s] REJ_BYTES16_APPEND_N) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  W(fun gl ->
    let th = REWRITE_RULE [REJX4_ABBREV m gl]
             (ISPECL [mk_comb(`shake128`,inp); `i:num`] REJX4_SAMPLE_SUC) in
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN
    MP_TAC(AP_TERM `LENGTH:(16 word)list->num` th)) THEN
  REWRITE_TAC[LENGTH_APPEND; ASSUME lenl1] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [LENGTH_SUB_LIST] THEN
  REWRITE_TAC[SUB_0] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[SYM th]));;
(*** For a polynomial with 256 samples already, those after one more ***)
(*** block, which are the same                                       ***)

let REJX4_SKIP_TAC m =
  let inp = el m REJX4_INPS in
  let c = mk_var("ci"^string_of_int m,`:num`) in
  let d0 = rejx4_done m `i:num` and d1 = rejx4_done m `i + 1` in
  SUBGOAL_THEN d0 ASSUME_TAC THENL
   [W(fun gl -> MP_TAC(REJX4_ABBREV m gl)) THEN
    REWRITE_TAC[ASSUME(mk_eq(c,`256`));
                ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`];
    ALL_TAC] THEN
  SUBGOAL_THEN d1 ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC (rejx4_count inp `i:num`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REJ_COUNT_MONO THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`MIN 256`,rejx4_count inp `i + 1`),`256`))
   (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THENL
   [ASM_REWRITE_TAC[ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`]; ALL_TAC] THEN
  MP_TAC(ISPECL [mk_comb(`shake128`,inp); `i:num`; `i + 1`]
                REJ_SAMPLE_FINAL) THEN
  ASM_REWRITE_TAC[ARITH_RULE `i <= i + 1`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME(mk_eq(c,`256`))]);;

(*** Whether there are 256 samples for all four after one more block ***)

let REJX4_LS_TAC =
  SUBGOAL_THEN (mk_eq(`i + 1 < k0`,mk_neg(REJX4_DONE `i + 1`)))
   ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[TAUT `(a <=> ~b) <=> (b <=> ~a)`] THEN EQ_TAC THENL
     [DISCH_THEN(fun dth -> DISCH_THEN(fun lth ->
        REJX4_MINIMALITY_TAC `i + 1` THEN REWRITE_TAC[dth; lth]));
      DISCH_TAC THEN SUBGOAL_THEN `i + 1 = k0` SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`i < k0`; `~(i + 1 < k0)`] THEN ARITH_TAC;
        REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* Simulating the code of the loop body for each polynomial in turn, until   *)
(* the PC is one of the targets: one step at a time, deciding the branches,  *)
(* and the copy of the loop as a whole from its header.                      *)
(* ------------------------------------------------------------------------- *)


(*** The facts about whether a polynomial has 256 samples ***)

let REJX4_IS_DONE_FACT tm =
  let tm' = if is_neg tm then dest_neg tm else tm in
  is_binary "<=" tm' && lhand tm' = `256`;;


let rejx4_ci m = mk_var("ci"^string_of_int m,`:num`);;

let REJX4_CIFLAG m =
  mk_cond(mk_binop `(<):num->num->bool` (rejx4_ci m) `256`,`word 1:int64`,`word 0:int64`);;

(*** After the first j polynomials (j >= 1), the samples for those after ***)
(*** one more block and for the others before it                         ***)

let REJX4_MID j =
  let t1 = list_mk_conj(REJX4_POLYS REJX4_CTRS (0--(j-1))) in
  let t1 = vsubst [`i + 1`,`i:num`] t1 in
  let rest m =
    let r = el m REJX4_CTRS and vec = el m REJX4_VECS
    and inp = el m REJX4_INPS
    and c = rejx4_ci m in
    vsubst [r,`R:(armstate,int64)component`; vec,`vec:int64`;
            inp,`inp:byte list`; c,`c:num`]
     `read (R:(armstate,int64)component) s = word c /\
      read (memory :> bytes(vec,2 * c)) s =
      num_of_wordlist(SUB_LIST(0,256) (REJ_SAMPLE(wordlist_of_num
        (336 + 112 * i)
        (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * i))))))` in
  let st m =
    vsubst [REJX4_ST m,`st:int64`; el m REJX4_SVS,`S:1600 word`]
     `read (memory :> bytes(st,200)) s =
      val(keccak_squeeze (3 + i + 1) (S:1600 word))` in
  let blk m =
    vsubst [REJX4_BUF m,`buf:int64`; el m REJX4_SVS,`S:1600 word`]
     `read (memory :> bytes(buf,168)) s =
      val(keccak_squeeze (3 + i + 1) (S:1600 word)) MOD 2 EXP (8 * 168)` in
  let flag32 =
    mk_eq(vsubst [REJX4_SP 60,`a:int64`]
            `read (memory :> bytes32 a) s`,
          mk_cond(mk_binop `(<):num->num->bool` (rejx4_ci 1) `256`,
                  `word 1:int32`,`word 0:int32`)) in
  mk_abs(`s:armstate`,
    list_mk_conj(conjuncts t1 @
                 flat(map (conjuncts o rest) (j--3)) @
                 map blk (j--3) @
                 map st (0--3) @
                 [mk_eq(`read X14 s`,REJX4_CIFLAG 2);
                  mk_eq(`read X25 s`,REJX4_CIFLAG 3);
                  flag32;
                  mk_eq(`read X24 s`,REJX4_BUF 0);
                  `read X19 s = vec3`; `read X20 s = vec2`;
                  `read X15 s = vec1`] @
                 conjuncts(REJX4_SLOTS()) @
                 conjuncts(REJX4_FRAME())));;

let REJX4_FLAG_ZX_STMT =
  `(!c. word_zx(word_zx(if c then word 1 else word 0:int64):int32):int64 =
        (if c then word 1 else word 0)) /\
   (!c. word_zx(if c then word 1 else word 0:int64):int32 =
        (if c then word 1 else word 0)) /\
   (!x. word_zx(if 256 <= x then word 0 else word 1:int32):int64 =
        (if x < 256 then word 1 else word 0))`;;
let REJX4_FLAG_ZX = prove(REJX4_FLAG_ZX_STMT,
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV;
    GEN_TAC THEN COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV;
    GEN_TAC THEN ASM_CASES_TAC `256 <= x` THEN
    ASM_REWRITE_TAC[GSYM NOT_LE] THEN CONV_TAC WORD_REDUCE_CONV]);;

let REJX4_PC_RULE_TAC =
  let pat = `read PC (s:armstate) = x:int64` in
  fun ths ->
    RULE_ASSUM_TAC(fun th ->
      if can (term_match [] pat) (concl th)
      then REWRITE_RULE ths th else th);;

let REJX4_HEADERS =
  map (fun k -> rej_target (REJX4_LOOP_DATA k).rej_header,k - 6) [6;7;8;9];;

(*** The copy of the loop for polynomial m, from its header ***)

let REJX4_LOOPI_TAC call m n =
  let inp = el m REJX4_INPS in
  let c = rejx4_ci m in
  let l = REJX4_LOOP_DATA (m + 6) in
  REJX4_BLOCK_TAC m (mk_var("s"^string_of_int(n-1),`:armstate`)) THEN
  call (m + 6)
   [rejx4_read l.rej_out; c; rejx4_read l.rej_base; `168`;
    rejx4_block inp `i:num`; `pc:num`] n THEN
  REJX4_COMBINE_TAC m (mk_var("s"^string_of_int n,`:armstate`)) THEN
  (if l.rej_full = l.rej_end then ALL_TAC else
   let d1 = rejx4_done m `i + 1` in
   ASM_CASES_TAC d1 THEN
   FIRST_ASSUM(fun th ->
     REJX4_PC_RULE_TAC [ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`; th]));;

(*** Step until the PC is a target, running a copy of the loop at its ***)
(*** header                                                            ***)

let rec REJX4_BODY_RUN_TAC call targets (asl,w) =
  let p = current_pc (asl,w) in
  if mem p targets then ALL_TAC (asl,w) else
  if find_terms is_cond p <> [] then
    failwith "REJX4_BODY_RUN_TAC: undecided branch" else
  let n = current_state_num (asl,w) + 1 in
  let tac = try REJX4_LOOPI_TAC call (assoc p REJX4_HEADERS) n
            with Failure _ -> REJX4_STEP_TAC n in
  (tac THEN REJX4_BODY_RUN_TAC call targets) (asl,w);;

(*** The stage for polynomial m: skipped if it has 256 samples already ***)

let REJX4_STAGE_TAC call m targets =
  let c = rejx4_ci m in
  let d0 = rejx4_done m `i:num` in
  ASM_CASES_TAC (mk_eq(c,`256`)) THENL
   [REJX4_SKIP_TAC m THEN
    REJ_READ_RULE_TAC(REWRITE_RULE[LT_REFL; COND_CLAUSES]);
    SUBGOAL_THEN (mk_binop `(<):num->num->bool` c `256`) ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN (mk_neg d0) ASSUME_TAC THENL
     [W(fun gl -> MP_TAC(REJX4_ABBREV m gl)) THEN
      POP_ASSUM MP_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    REJ_READ_RULE_TAC(REWRITE_RULE[ASSUME(mk_binop `(<):num->num->bool` c `256`);
                                   COND_CLAUSES])] THEN
  REJX4_BODY_RUN_TAC call (map rejx4_label targets);;

let REJX4_BODY0_TAC : tactic = fun g ->
  (ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_EXEC (1--11) THEN
  REJX4_NORMALIZE_TAC THEN
  MAP_EVERY (fun m -> KECCAK_STATE_AT_TAC (REJX4_ST m)) (0--3) THEN
  LOCAL_SQUEEZE_X4_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `1`; `read X5 s`;
    `keccak_squeeze (3 + i) (S0:1600 word)`;
    `keccak_squeeze (3 + i) (S1:1600 word)`;
    `keccak_squeeze (3 + i) (S2:1600 word)`;
    `keccak_squeeze (3 + i) (S3:1600 word)`;
    `pc:num`; `read SP s`; `read X30 s`] 12 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600; MULT_CLAUSES;
                              REJ_NSUM_1; EXP; ADD_CLAUSES;
                              KECCAK_SQUEEZE_ADD;
                              ARITH_RULE `1 + 3 + i = 3 + i + 1`]) THEN
  REJX4_NORMALIZE_TAC THEN
  REJX4_STAGE_TAC REJX4_LOOP_CALL 0 ["loop6_exit2"] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[REJX4_FLAG_ZX]) g;;

let REJX4_BODY1_TAC =
  ENSURES_INIT_TAC "s0" THEN
  REJX4_STAGE_TAC REJX4_LOOP_CALL 1 ["loop7_exit"] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[REJX4_FLAG_ZX];;

let REJX4_BODY2_TAC =
  ENSURES_INIT_TAC "s0" THEN
  REJX4_STAGE_TAC REJX4_LOOP_CALL 2 ["loop8_exit"] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[REJX4_FLAG_ZX];;

let REJX4_BODY3_TAC =
  ENSURES_INIT_TAC "s0" THEN
  REJX4_STAGE_TAC REJX4_LOOP_CALL 3 ["loop9_exit"] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[REJX4_FLAG_ZX];;

let REJX4_DONE_FACT m c =
  let cnt = rejx4_count (el m REJX4_INPS) c in
  (SUBGOAL_THEN (mk_eq(mk_comb(`MIN 256`,cnt),`256`))
    (fun th -> REJ_READ_RULE_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THENL
    [REWRITE_TAC[ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
     FIRST_ASSUM ACCEPT_TAC;
     ALL_TAC]);;

let REJX4_TODO_FACT m c =
  let cnt = rejx4_count (el m REJX4_INPS) c in
  let d = mk_binop `(<=):num->num->bool` `256` cnt in
  SUBGOAL_THEN (mk_binop `(<):num->num->bool` cnt `256`) ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if concl th = mk_neg d then MP_TAC th else NO_TAC) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REJ_MIN_FACT_TAC cnt;;

let REJX4_TAIL_RUN_TAC =
  REJX4_BODY_RUN_TAC REJX4_LOOP_CALL
   [rejx4_label "loop5"; rejx4_label "loop5_exit"] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[REJX4_FLAG_ZX];;

let REJX4_TAIL_TAC =
  let c = `i + 1` in
  let d m = rejx4_done m c in
  ENSURES_INIT_TAC "s0" THEN
  ASM_CASES_TAC (d 0) THENL
   [REJX4_DONE_FACT 0 c THEN
    ASM_CASES_TAC (d 1) THENL
     [REJX4_DONE_FACT 1 c THEN
      ASM_CASES_TAC (d 2) THENL
       [REJX4_DONE_FACT 2 c THEN
        ASM_CASES_TAC (d 3) THENL
         [REJX4_DONE_FACT 3 c THEN REJX4_TAIL_RUN_TAC;
          REJX4_TODO_FACT 3 c THEN REJX4_TAIL_RUN_TAC];
        REJX4_TODO_FACT 2 c THEN REJX4_TAIL_RUN_TAC];
      REJX4_TODO_FACT 1 c THEN REJX4_TAIL_RUN_TAC];
    REJX4_TODO_FACT 0 c THEN REJX4_TAIL_RUN_TAC];;

let REJX4_EXIT_TAC =
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun inp ->
    SUBGOAL_THEN (mk_eq(mk_comb(`MIN 256`,rejx4_count inp `k0:num`),`256`))
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC]) REJX4_INPS THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  MAP_EVERY (fun inp ->
    MP_TAC(ISPECL [mk_comb(`shake128`,inp); `k0:num`; `k:num`]
                  REJ_SAMPLE_FINAL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC])
   REJX4_INPS THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let REJX4_FINAL_TAC =
  let tac inp =
    let l = mk_comb(`SUB_LIST(0,256):(16 word)list->(16 word)list`,
                    mk_comb(`REJ_SAMPLE`,rejx4_fields inp `k:num`)) in
    let lth = mk_eq(mk_comb(`LENGTH:(16 word)list->num`,l),`256`) in
    SUBGOAL_THEN lth ASSUME_TAC THENL
     [REWRITE_TAC[LENGTH_SUB_LIST; SUB_0;
                  ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [SYM(ASSUME lth)] THEN
    MATCH_MP_TAC REJ_WORDLIST_OF_BYTES16 THEN REWRITE_TAC[ASSUME lth] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] in
  REPEAT CONJ_TAC THENL map tac REJX4_INPS;;

let REJX4_PART3_TAC =
  ENSURES_INIT_TAC "s0" THEN REJX4_GOT_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_EXEC (1--2) THEN
  LOCAL_RELEASE_X4_TAC
   [`read X0 s`; `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
    `read SP s`; `read X30 s`] 3 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_EXEC (4--8) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_EXEC 8 THEN
  LIBC_CALL_TAC "H_MEMSET" MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 13 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_EXEC [14] THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_EXEC (15--27) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REJX4_FINAL_TAC;;

(*** From the entry to loop4_exit, through the first three blocks ***)

let REJX4_PART1_TAC : tactic = fun g ->
  (ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_EXEC (1--9) THEN
  REJX4_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_EXEC [10] THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_EXEC (11--20) THEN
  REJX4_NORMALIZE_TAC THEN
  LOCAL_INIT_X4_TAC [`read X0 s`; `pc:num`; `read X30 s`] 21 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_EXEC (22--28) THEN
  REJX4_NORMALIZE_TAC THEN REJX4_GOT_TAC THEN
  LOCAL_ABSORB_X4_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`; `34`;
    `num_of_bytelist(inp0:byte list)`; `num_of_bytelist(inp1:byte list)`;
    `num_of_bytelist(inp2:byte list)`; `num_of_bytelist(inp3:byte list)`;
    `guard:int64`; `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
    `read SP s`; `read X30 s`] 29 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_EXEC (30--39) THEN
  REJX4_NORMALIZE_TAC THEN
  MAP_EVERY (fun m -> KECCAK_STATE_AT_TAC (REJX4_ST m)) (0--3) THEN
  LOCAL_SQUEEZE_X4_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `3`; `read X5 s`;
    `S0:1600 word`; `S1:1600 word`; `S2:1600 word`; `S3:1600 word`;
    `pc:num`; `read SP s`; `read X30 s`] 40 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  REJX4_NORMALIZE_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_EXEC (41--42) THEN
  REJX4_NORMALIZE_TAC THEN
  MAP_EVERY (fun m ->
    (if m = 0 then ALL_TAC else
     ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_EXEC
      ((4 * m + 40)--(4 * m + 42)) THEN
     REJX4_NORMALIZE_TAC) THEN
    REJX4_INPUT0_TAC m (mk_var("s"^string_of_int(4 * m + 42),`:armstate`)) THEN
    REJX4_LOOP0_TAC m (4 * m + 43)) (0--3) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]) g;;

(*** The body of loop5, from 3 + i blocks of each to 3 + i + 1 ***)

let REJX4_SEQ pcterm j : tactic = fun g ->
  ENSURES_SEQUENCE_TAC pcterm (REJX4_MID j) g;;

let REJX4_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REJX4_LS_TAC THEN REJX4_ABBREV_TAC THEN
  REJX4_SEQ `pc + mlkem_poly_rej_uniform_x4_loop6_exit2` 1 THEN CONJ_TAC THENL
   [REJX4_BODY0_TAC;
    REJX4_SEQ `pc + mlkem_poly_rej_uniform_x4_loop7_exit` 2 THEN CONJ_TAC THENL
     [REJX4_BODY1_TAC;
      REJX4_SEQ `pc + mlkem_poly_rej_uniform_x4_loop8_exit` 3 THEN CONJ_TAC THENL
       [REJX4_BODY2_TAC;
        REJX4_SEQ `pc + mlkem_poly_rej_uniform_x4_loop9_exit` 4 THEN CONJ_TAC THENL
         [REJX4_BODY3_TAC; REJX4_TAIL_TAC]]]];;

(*** loop5, if more blocks are needed ***)

let REJX4_LOOP_TAC : tactic = fun g ->
  (ENSURES_WHILE_UP2_TAC `k0:num` `pc + mlkem_poly_rej_uniform_x4_loop5`
   `pc + mlkem_poly_rej_uniform_x4_loop5_exit` (REJX4_INV()) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; REJX4_ENTER_TAC; REJX4_BODY_TAC; REJX4_EXIT_TAC]) g;;

let REJX4_SEQ2 : tactic = fun g ->
  (ENSURES_SEQUENCE_TAC `pc + mlkem_poly_rej_uniform_x4_loop5_exit`
    (REJX4_A2())) g;;

let REJX4_SEQ3 : tactic = fun g ->
  (ENSURES_SEQUENCE_TAC `pc + mlkem_poly_rej_uniform_x4_loop4_exit`
    (REJX4_A3())) g;;

let REJX4_CORRECT_TAC =
  REJX4_INTRO_TAC THEN
  REJX4_CASES_TAC
   (REJX4_SETUP_TAC THEN REJX4_ABSORBED_TAC THEN REJX4_MINIMAL_TAC THEN

    (*** The first three blocks of each and the samples from them ***)

    REJX4_SEQ2 THEN CONJ_TAC THENL
     [REJX4_SEQ3 THEN CONJ_TAC THENL
       [REJX4_PART1_TAC;
        ASM_CASES_TAC `k0 = 0` THENL [REJX4_NOLOOP_TAC; REJX4_LOOP_TAC]];
      REJX4_PART3_TAC]);;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REJX4_CORRECT_TAC);;


let PREJ4_ARGS =
  [`vec0:int64`; `vec1:int64`; `vec2:int64`; `vec3:int64`;
   `seed:int64`; `inp0:byte list`; `inp1:byte list`;
   `inp2:byte list`; `inp3:byte list`; `guard:int64`;
   `mf:int64`; `pc:num`; `stackpointer:int64`; `returnaddress:int64`];;

let PREJ4_LEAVES = ref ([]:term list);;

(*** The template for the events, with its leaves, for one of the two  ***)
(*** cases for the alignment of the stack pointer, the leaves of each  ***)
(*** with a suffix. The events of an iteration of loop5 depend on      ***)
(*** which polynomials already have 256 samples (first test of each    ***)
(*** stage), on the exit taken by loop6 and on the tests at the end,   ***)
(*** all functions of the seeds                                        ***)

let PREJ4_TEMPLATE_BODY suf =
  let args = PREJ4_ARGS in
  let fty = itlist (fun a t -> mk_fun_ty (type_of a) t) args
                   `:(uarch_event)list` in
  let ftyi = itlist (fun a t -> mk_fun_ty (type_of a) t) args
                    (mk_fun_ty `:num` `:(uarch_event)list`) in
  let app n = list_mk_comb(mk_var("f_ev_" ^ n ^ suf,fty),args) in
  let leaf code =
    let v = mk_var("f_ev_loop_" ^ code ^ suf,ftyi) in
    PREJ4_LEAVES := v :: !PREJ4_LEAVES;
    mk_comb(list_mk_comb(v,args),`i:num`) in
  let k0 = mk_comb(`(minimal):(num->bool)->num`,
                   mk_abs(`n:num`,REJX4_DONE `n:num`)) in
  let d m = rejx4_done m `i:num` and e m = rejx4_done m `i + 1` in
  let cnd c a b = mk_cond(c,a,b) in
  let ap = `APPEND:(uarch_event)list->(uarch_event)list->(uarch_event)list` in
  let apl l = end_itlist (fun a b -> list_mk_comb(ap,[a;b])) l in
  let seg0 = cnd (d 0) (leaf "0s") (cnd (e 0) (leaf "0f") (leaf "0r")) in
  let seg m = cnd (d m) (leaf (string_of_int m ^ "s"))
                         (leaf (string_of_int m ^ "r")) in
  let tail =
    cnd (e 0)
     (cnd (e 1)
       (cnd (e 2) (cnd (e 3) (leaf "t4") (leaf "t3")) (leaf "t2"))
       (leaf "t1"))
     (leaf "t0") in
  let loop = mk_abs(`i:num`,apl [tail; seg 3; seg 2; seg 1; seg0]) in
  let enum = list_mk_comb(`ENUMERATEL:num->(num->(uarch_event)list)->
                                     (uarch_event)list`,[k0;loop]) in
  let enter =
    cnd (rejx4_done0 0)
     (cnd (rejx4_done0 1)
       (cnd (rejx4_done0 2) (app "enter3") (app "enter2"))
       (app "enter1"))
     (app "enter0") in
  let mid = mk_cond(mk_eq(k0,`0`),app "skip",
              apl [app "exit"; enum; enter]) in
  apl [app "p3"; mid; app "p1"];;

let PREJ4_SAFE_TEMPLATE =
  let ba = PREJ4_TEMPLATE_BODY "_a" in
  let bb = PREJ4_TEMPLATE_BODY "_b" in
  list_mk_abs(PREJ4_ARGS,
    mk_cond(`aligned 32 (stackpointer:int64)`,ba,bb));;

let PREJ4_SAFE_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    let sth = CONJUNCT2(MATCH_MP MEMSET_FULL_CONTRACT th) in
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[memset_safety_contract] sth) "H_MEMSET" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLKEM_NATIVE_SHAKE128X4_RELEASE_CLANG17_O2_IMAGE_SUBROUTINE_SAFE
               sth) "H_RELEASE") THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP
       MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_CLANG17_O2_IMAGE_SUBROUTINE_FULL th)
     "H_ABSORB") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHAKE128X4_INIT_CLANG17_O2_IMAGE_SUBROUTINE_SAFE "H_INIT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O2_IMAGE_SUBROUTINE_FULL
    "H_SQUEEZE" THEN
  MAP_EVERY (fun (k,th) ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC th ("H_LOOP" ^ string_of_int k))
   (zip [1;2;3;4;6;7;8;9]
        MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_LOOPS_FULL) THEN
  CONCRETIZE_F_EVENTS_TAC PREJ4_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              GSYM REJ_SAMPLE] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

(*** In each of the two cases, the template is the one for the case ***)

let PREJ4_CASE_TAC =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if c = `aligned 32 (stackpointer:int64)` ||
       c = `~(aligned 32 (stackpointer:int64))`
    then REWRITE_TAC[th] else NO_TAC);;

let PREJ4_ALLOWED () =
  [`pc:num`; `vec0:int64`; `vec1:int64`; `vec2:int64`; `vec3:int64`;
   `seed:int64`; `inp0:byte list`; `inp1:byte list`; `inp2:byte list`;
   `inp3:byte list`; `guard:int64`; `mf:int64`; `stackpointer:int64`;
   `returnaddress:int64`; `i:num`; `k0:num`; `e2:(uarch_event)list`;
   `ci0:num`; `ci1:num`; `ci2:num`; `ci3:num`] @ !PREJ4_LEAVES;;

let PREJ4_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_clang17_O2_mc,
       MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_EXEC,
       0x0,mlkem_native_libmlkem_clang17_O2_mc,safety_th)
      ilist n THENL
     [REJX4_ADDRESS_TAC THEN EXISTS_E2_TAC (ref (PREJ4_ALLOWED()));
      LABEL_TAC name safety_th]);;

let PREJ4_LOOP_CALL k ilist n =
  PREJ4_SAFE_CALL_TAC ("H_LOOP" ^ string_of_int k)
   (`e:(uarch_event)list` :: ilist) n;;

let PREJ4_LOOP0_TAC = REJX4_LOOP0_GEN_TAC PREJ4_LOOP_CALL;;

(*** DISCHARGE_SAFETY_PROPERTY_TAC, with only the facts about events    ***)
(*** for the check of the memory accesses (see PREJ_DISCHARGE_TAC for   ***)
(*** the reasons). The existential witness for the events is renamed    ***)
(*** first to a name used nowhere else                                  ***)

(*** The first events of a segment, one cell for each instruction, are  ***)
(*** grouped into one list, so that they match the event function of    ***)
(*** the segment (the unification of the events handles up to three      ***)
(*** cells)                                                              ***)

let PREJ4_GROUP_TAC : tactic = fun (asl,w) ->
  let eq = if is_conj w then fst(dest_conj w) else w in
  if not(is_eq eq) then ALL_TAC (asl,w) else
  let l = lhs eq in
  let rec walk t acc =
    match t with
      Comb(Comb(Const("APPEND",_),Comb(Comb(Const("CONS",_),h),Const("NIL",_))),
           rest) -> walk rest (h::acc)
    | Comb(Comb(Const("CONS",_),h),rest) -> walk rest (h::acc)
    | _ -> (rev acc,t) in
  let pre,tl = walk l [] in
  if length pre < 2 then ALL_TAC (asl,w) else
  let lst = mk_list(pre,`:uarch_event`) in
  let app = mk_comb(mk_comb(`APPEND:(uarch_event)list->(uarch_event)list->
                                    (uarch_event)list`,lst),tl) in
  (SUBGOAL_THEN (mk_eq(l,app)) (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[APPEND]; ALL_TAC]) (asl,w);;

let PREJ4_META_COUNT = ref 0;;

let PREJ4_DISCHARGE_TAC =
  CONV_TAC(DEPTH_CONV PREJ_CONS_CONV) THEN
  REWRITE_TAC[ENUMERATEL_APPEND_ZERO; APPEND_NIL; CONJUNCT1 APPEND;
              GSYM APPEND_ASSOC] THEN
  W(fun (asl,w) ->
    let v,_ = dest_exists w in
    PREJ4_META_COUNT := !PREJ4_META_COUNT + 1;
    CONV_TAC(GEN_ALPHA_CONV
      (mk_var("e2_seg" ^ string_of_int(!PREJ4_META_COUNT),type_of v)))) THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  REWRITE_TAC[APPEND_NIL; CONJUNCT1 APPEND; GSYM APPEND_ASSOC;
              SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  PREJ4_GROUP_TAC THEN
  W(fun (asl,w) ->
    (if is_conj w then CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]
     else ALL_TAC) THEN
    PREJ_KEEP_EVENTS_TAC THEN
    RULE_ASSUM_TAC(fun th ->
      if is_eq(concl th) && lhs(concl th) = `e2:(uarch_event)list`
      then REWRITE_RULE[GSYM APPEND_ASSOC] th else th) THEN
    REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

(*** The numbers of samples so far in terms of the seeds again, as the  ***)
(*** events must not depend on the abbreviations                       ***)

let PREJ4_UNABBREV_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let cs = CONJUNCTS th in
    if exists (REJX4_IS_ABBREV o concl) cs then
      MAP_EVERY (fun c -> if REJX4_IS_ABBREV(concl c)
                          then SUBST_ALL_TAC(SYM c) else ASSUME_TAC c) cs
    else NO_TAC));;

(*** The events of a part of an iteration, with the conditions decided ***)

let PREJ4_SEG_DISCHARGE_TAC =
  REJ_DECIDE_CONDS_TAC THEN REJ_DECIDE_CONDS_TAC THEN
  PREJ4_UNABBREV_TAC THEN PREJ4_DISCHARGE_TAC;;

let PREJ4_FINAL_TAC ths =
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC ths THEN
  ASM_REWRITE_TAC[REJX4_FLAG_ZX];;

(*** From the entry to loop4_exit ***)

let PREJ4_SAFE_PART1_TAC : tactic = fun g ->
  (REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_EXEC (1--9) THEN
  REJX4_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_EXEC [10] THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_EXEC (11--20) THEN
  REJX4_NORMALIZE_TAC THEN
  PREJ4_SAFE_CALL_TAC "H_INIT"
   [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read X30 s`] 21 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_EXEC (22--28) THEN
  REJX4_NORMALIZE_TAC THEN REJX4_GOT_TAC THEN
  PREJ4_SAFE_CALL_TAC "H_ABSORB"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X3 s`; `read X4 s`; `34`;
    `num_of_bytelist(inp0:byte list)`; `num_of_bytelist(inp1:byte list)`;
    `num_of_bytelist(inp2:byte list)`; `num_of_bytelist(inp3:byte list)`;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 29 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_EXEC (30--39) THEN
  REJX4_NORMALIZE_TAC THEN
  MAP_EVERY (fun m -> KECCAK_STATE_AT_TAC (REJX4_ST m)) (0--3) THEN
  PREJ4_SAFE_CALL_TAC "H_SQUEEZE"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X3 s`; `3`; `read X5 s`;
    `S0:1600 word`; `S1:1600 word`; `S2:1600 word`; `S3:1600 word`;
    `pc:num`; `read SP s`; `read X30 s`] 40 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  REJX4_NORMALIZE_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_EXEC (41--42) THEN
  REJX4_NORMALIZE_TAC THEN
  MAP_EVERY (fun m ->
    (if m = 0 then ALL_TAC else
     ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_EXEC
      ((4 * m + 40)--(4 * m + 42)) THEN
     REJX4_NORMALIZE_TAC) THEN
    REJX4_INPUT0_TAC m (mk_var("s"^string_of_int(4 * m + 42),`:armstate`)) THEN
    PREJ4_LOOP0_TAC m (4 * m + 43)) (0--3) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  PREJ4_DISCHARGE_TAC) g;;

(*** If no more block is needed, to the exit of loop5 ***)

let PREJ4_SAFE_NOLOOP_TAC =
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES; ADD_CLAUSES]) THEN
  REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  MAP_EVERY (fun inp ->
    let c = mk_comb(`MIN 256`,rejx4_count0 inp) in
    SUBGOAL_THEN (mk_eq(c,`256`))
     (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[ARITH_RULE `MIN a b = a <=> a <= b`] THEN ASM_REWRITE_TAC[];
      ALL_TAC]) REJX4_INPS THEN
  REJX4_RUN_TAC [rejx4_label "loop5_exit"] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun inp ->
    MP_TAC(ISPECL [mk_comb(`shake128`,inp); `0`; `k:num`]
                  REJ_SAMPLE_FINAL) THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LE_0] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC]) REJX4_INPS THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  ASM_REWRITE_TAC[] THEN PREJ4_DISCHARGE_TAC;;

(*** If more blocks are needed, from loop4_exit to the header of loop5 ***)

let PREJ4_ENTER_RUN_TAC =
  REJX4_RUN_TAC [rejx4_label "loop5"] THEN
  REJX4_NORMALIZE_TAC THEN
  PREJ4_FINAL_TAC [MULT_CLAUSES; ADD_CLAUSES] THEN
  REJ_DECIDE_CONDS_TAC THEN REWRITE_TAC[ENUMERATEL_APPEND_ZERO] THEN
  PREJ4_DISCHARGE_TAC;;

let PREJ4_SAFE_ENTER_TAC =
  SUBGOAL_THEN (mk_neg(rhs(concl(REWRITE_CONV[MULT_CLAUSES; ADD_CLAUSES]
                                  (REJX4_DONE `0`)))))
   ASSUME_TAC THENL
   [REJX4_MINIMALITY_TAC `0` THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `~(k0 = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  PREJ_E2_TAC THEN
  ASM_CASES_TAC (rejx4_done0 0) THENL
   [REJX4_DONE0_FACT 0 THEN
    ASM_CASES_TAC (rejx4_done0 1) THENL
     [REJX4_DONE0_FACT 1 THEN
      ASM_CASES_TAC (rejx4_done0 2) THENL
       [REJX4_DONE0_FACT 2 THEN
        SUBGOAL_THEN (mk_neg(rejx4_done0 3)) ASSUME_TAC THENL
         [FIRST_ASSUM(fun th ->
            if is_neg(concl th) && is_conj(dest_neg(concl th))
            then MP_TAC th else NO_TAC) THEN
          REWRITE_TAC(map (fun m -> ASSUME(rejx4_done0 m)) [0;1;2]);
          ALL_TAC] THEN
        REJX4_TODO0_FACT 3 THEN PREJ4_ENTER_RUN_TAC;
        REJX4_TODO0_FACT 2 THEN PREJ4_ENTER_RUN_TAC];
      REJX4_TODO0_FACT 1 THEN PREJ4_ENTER_RUN_TAC];
    REJX4_TODO0_FACT 0 THEN PREJ4_ENTER_RUN_TAC];;

(*** The events of an iteration of loop5 as those of its parts: one of ***)
(*** the sequence points per stage, from the end of the iteration      ***)

let PREJ4_SPLIT_EVENTS_TAC =
  REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC];;

let PREJ4_STAGE_START_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  PREJ_E2_TAC;;

let PREJ4_SAFE_BODY0_TAC : tactic = fun g ->
  (PREJ4_STAGE_START_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_EXEC (1--11) THEN
  REJX4_NORMALIZE_TAC THEN
  MAP_EVERY (fun m -> KECCAK_STATE_AT_TAC (REJX4_ST m)) (0--3) THEN
  PREJ4_SAFE_CALL_TAC "H_SQUEEZE"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X3 s`; `1`; `read X5 s`;
    `keccak_squeeze (3 + i) (S0:1600 word)`;
    `keccak_squeeze (3 + i) (S1:1600 word)`;
    `keccak_squeeze (3 + i) (S2:1600 word)`;
    `keccak_squeeze (3 + i) (S3:1600 word)`;
    `pc:num`; `read SP s`; `read X30 s`] 12 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600; MULT_CLAUSES;
                              REJ_NSUM_1; EXP; ADD_CLAUSES;
                              KECCAK_SQUEEZE_ADD;
                              ARITH_RULE `1 + 3 + i = 3 + i + 1`]) THEN
  REJX4_NORMALIZE_TAC THEN
  REJX4_STAGE_TAC PREJ4_LOOP_CALL 0 ["loop6_exit2"] THEN
  PREJ4_FINAL_TAC [] THEN
  PREJ4_SEG_DISCHARGE_TAC) g;;

let PREJ4_SAFE_STAGE_TAC m target =
  PREJ4_STAGE_START_TAC THEN
  REJX4_STAGE_TAC PREJ4_LOOP_CALL m [target] THEN
  PREJ4_FINAL_TAC [] THEN
  PREJ4_SEG_DISCHARGE_TAC;;

(*** The end of an iteration, from the tests of the numbers of samples ***)

let PREJ4_TAIL_RUN_TAC =
  REJX4_BODY_RUN_TAC PREJ4_LOOP_CALL
   [rejx4_label "loop5"; rejx4_label "loop5_exit"] THEN
  PREJ4_FINAL_TAC [] THEN PREJ4_SEG_DISCHARGE_TAC;;

let PREJ4_SAFE_TAIL_TAC =
  let c = `i + 1` in
  let d m = rejx4_done m c in
  PREJ4_STAGE_START_TAC THEN
  ASM_CASES_TAC (d 0) THENL
   [REJX4_DONE_FACT 0 c THEN
    ASM_CASES_TAC (d 1) THENL
     [REJX4_DONE_FACT 1 c THEN
      ASM_CASES_TAC (d 2) THENL
       [REJX4_DONE_FACT 2 c THEN
        ASM_CASES_TAC (d 3) THENL
         [REJX4_DONE_FACT 3 c THEN PREJ4_TAIL_RUN_TAC;
          REJX4_TODO_FACT 3 c THEN PREJ4_TAIL_RUN_TAC];
        REJX4_TODO_FACT 2 c THEN PREJ4_TAIL_RUN_TAC];
      REJX4_TODO_FACT 1 c THEN PREJ4_TAIL_RUN_TAC];
    REJX4_TODO_FACT 0 c THEN PREJ4_TAIL_RUN_TAC];;

(*** A sequence point after the first j polynomials. The events of the ***)
(*** part after it are the first k components of the sequence of the   ***)
(*** events of the iteration; those before it, with the earlier ones,  ***)
(*** are the others                                                    ***)

let PREJ4_SEQ pcterm j k : tactic = fun (asl,w) ->
  let post = rand(rator w) in
  let ex = find_term (fun t -> is_exists t &&
             fst(dest_var(fst(dest_exists t))) = "e2") post in
  let v,bod = dest_exists ex in
  let c1,rest = dest_conj bod in
  let eq,c3 = dest_conj rest in
  let rec drop n t =
    if n = 0 then t else drop (n - 1) (snd(dest_binary "APPEND" t)) in
  let ex' = mk_exists(v,list_mk_conj[c1; mk_eq(lhs eq,drop k (rhs eq)); c3]) in
  let inv = let s,b = dest_abs (REJX4_MID j) in mk_abs(s,mk_conj(b,ex')) in
  ENSURES_SEQUENCE_TAC pcterm inv (asl,w);;

let PREJ4_SAFE_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REJX4_LS_TAC THEN REJX4_ABBREV_TAC THEN PREJ4_SPLIT_EVENTS_TAC THEN
  PREJ4_SEQ `pc + mlkem_poly_rej_uniform_x4_loop6_exit2` 1 4 THEN CONJ_TAC THENL
   [PREJ4_SAFE_BODY0_TAC;
    PREJ4_SEQ `pc + mlkem_poly_rej_uniform_x4_loop7_exit` 2 3 THEN
    CONJ_TAC THENL
     [PREJ4_SAFE_STAGE_TAC 1 "loop7_exit";
      PREJ4_SEQ `pc + mlkem_poly_rej_uniform_x4_loop8_exit` 3 2 THEN
      CONJ_TAC THENL
       [PREJ4_SAFE_STAGE_TAC 2 "loop8_exit";
        PREJ4_SEQ `pc + mlkem_poly_rej_uniform_x4_loop9_exit` 4 1 THEN
        CONJ_TAC THENL
         [PREJ4_SAFE_STAGE_TAC 3 "loop9_exit"; PREJ4_SAFE_TAIL_TAC]]]];;

let PREJ4_SAFE_EXIT_TAC =
  REWRITE_TAC[] THEN PREJ4_STAGE_START_TAC THEN
  MAP_EVERY (fun inp ->
    SUBGOAL_THEN (mk_eq(mk_comb(`MIN 256`,rejx4_count inp `k0:num`),`256`))
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC]) REJX4_INPS THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  MAP_EVERY (fun inp ->
    MP_TAC(ISPECL [mk_comb(`shake128`,inp); `k0:num`; `k:num`]
                  REJ_SAMPLE_FINAL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC])
   REJX4_INPS THEN
  PREJ4_FINAL_TAC [] THEN
  PREJ4_DISCHARGE_TAC;;

let PREJ4_SAFE_LOOP_TAC : tactic = fun g ->
  (REWRITE_TAC[EQF_INTRO(ASSUME `~(k0 = 0)`)] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `k0:num` `pc + mlkem_poly_rej_uniform_x4_loop5`
   `pc + mlkem_poly_rej_uniform_x4_loop5_exit` (REJX4_INV()) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    PREJ4_SAFE_ENTER_TAC;
    PREJ4_SAFE_BODY_TAC;
    PREJ4_SAFE_EXIT_TAC]) g;;

let PREJ4_SAFE_PART3_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `k0:num`)) THEN
  PREJ4_STAGE_START_TAC THEN
  REJX4_GOT_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_EXEC (1--2) THEN
  PREJ4_SAFE_CALL_TAC "H_RELEASE"
   [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read SP s`;
    `read X30 s`] 3 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_EXEC (4--8) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_EXEC 8 THEN
  (fun g -> LIBC_SAFE_CALL_TAC "H_MEMSET"
    MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref (PREJ4_ALLOWED())) 13 g) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_EXEC [14] THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_EXEC (15--27) THEN
  PREJ4_FINAL_TAC [] THEN
  RULE_ASSUM_TAC(fun th ->
    if is_eq(concl th) && lhs(concl th) = `e2:(uarch_event)list`
    then REWRITE_RULE[ADD_ASSOC] th else th) THEN
  REWRITE_TAC[ADD_ASSOC] THEN
  PREJ4_DISCHARGE_TAC;;

let PREJ4_SEQ2 : tactic = fun g ->
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_poly_rej_uniform_x4_loop5_exit`
    (REJX4_A2()) g;;

let PREJ4_SEQ3 : tactic = fun g ->
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_poly_rej_uniform_x4_loop4_exit`
    (REJX4_A3()) g;;

let PREJ4_SAFE_TAC =
  PREJ4_SAFE_INTRO_TAC THEN
  REJX4_CASES_TAC
   (PREJ4_CASE_TAC THEN REJX4_SETUP_TAC THEN REJX4_ABSORBED_TAC THEN
    REJX4_MINIMAL_TAC THEN
    PREJ4_SEQ2 THEN CONJ_TAC THENL
     [PREJ4_SEQ3 THEN CONJ_TAC THENL
       [PREJ4_SAFE_PART1_TAC;
        ASM_CASES_TAC `k0 = 0` THENL
         [PREJ4_SAFE_NOLOOP_TAC; PREJ4_SAFE_LOOP_TAC]];
      PREJ4_SAFE_PART3_TAC]);;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  PREJ4_SAFE_TAC);;
