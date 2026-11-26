(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The Keccak-f1600 permutation: the proof (see keccakf1600_permute_spec.ml). *)
(* The code of clang 23 has the loop of the gcc code of the x86 gcc12_O2     *)
(* image of mlkem-native, with two rounds in each of its 12 iterations,      *)
(* but it keeps the lanes of the state partly in registers and partly in the *)
(* stack, in other places, and the counter of the loop in a stack slot, with *)
(* the table of round constants addressed by it. So the proof is that of     *)
(* x86/proofs/mldsa_native/gcc12_O2_reduced_ram/keccakf1600_permute_proof.ml *)
(* with the places of the lanes and the invariant changed, and done in the   *)
(* image, where the table is at pc + rodata_mld_KeccakF_RoundConstants.      *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/keccakf1600_permute_spec.ml";;
needs "x86/proofs/utils/mldsa_native_full.ml";;
needs "x86/proofs/utils/mldsa_native_prefix.ml";;
needs "x86/proofs/utils/keccak_fips202.ml";;

let PERM_EXEC = MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;

(* ------------------------------------------------------------------------- *)
(* Reading the round constants from the table in the image.                  *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES64_NUM_OF_WORDLIST = prove
 (`!a:int64 (l:int64 list) n j s:x86state.
        read (memory :> bytes(a,8 * n)) s = num_of_wordlist l /\
        LENGTH l = n /\ j < n
        ==> read (memory :> bytes64(word_add a (word(8 * j)))) s = EL j l`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  MP_TAC(ISPECL [`l:int64 list`; `j:num`] NUM_OF_WORDLIST_EL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && is_comb(lhs(concl th)) &&
       can (term_match [] `read c s`) (lhs(concl th))
    then REWRITE_TAC[GSYM th] else failwith "") THEN
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `64 * j = 8 * (8 * j)`;
              ARITH_RULE `18446744073709551616 = 2 EXP (8 * 8)`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;


let KECCAK_RC_IMAGE_VALUE =
  let th = MLD_PREFIX_IMAGE_BYTES_RULE
             mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
             (layout "rodata_mld_KeccakF_RoundConstants") 192 in
  let n = rand(concl(UNDISCH(SPEC_ALL th))) in
  let eq = prove(mk_eq(`num_of_wordlist round_constants`,n),
    REWRITE_TAC[round_constants; num_of_wordlist] THEN
    CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV) in
  REWRITE_RULE[GSYM eq] th;;

let LENGTH_ROUND_CONSTANTS = prove
 (`LENGTH round_constants = 24`,
  REWRITE_TAC[round_constants; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;


(* ------------------------------------------------------------------------- *)
(* Tactics for the loop body, which does two rounds. As each lane of the     *)
(* first round is computed, it is replaced by a variable E_j abbreviating    *)
(* the corresponding lane in the specification, so that the second round     *)
(* and the final checks are about one round only. The lanes are recognized   *)
(* by evaluating both sides at random values, before proving the equations   *)
(* with KECCAK_BITBLAST_TAC.                                                 *)
(* ------------------------------------------------------------------------- *)

(*** Introduce ghost variables for the state reads in a list ***)

let GHOST_STATELIST_TAC =
  W(fun (asl,w) ->
        let regreads = dest_list(find_term is_list w) in
        let ghostvars = make_args "Ai_" [] (map type_of regreads) in
        EVERY(map2 GHOST_INTRO_TAC ghostvars (map rator regreads)));;

(*** Evaluation of 64-bit word expressions, with random values for atoms ***)

let eval64 =
  let atom_vals = Hashtbl.create 100 and memo = Hashtbl.create 10000 in
  let rand64 () =
    Int64.logor (Int64.shift_left (Int64.of_int (Random.bits ())) 34)
     (Int64.logor (Int64.shift_left (Int64.of_int (Random.bits ())) 4)
                  (Int64.of_int (Random.bits () land 15))) in
  let atom_val t =
    try Hashtbl.find atom_vals t with Not_found ->
      let v = rand64 () in Hashtbl.add atom_vals t v; v in
  let ror64 x n =
    if n = 0 then x else
    Int64.logor (Int64.shift_right_logical x n)
                (Int64.shift_left x (64 - n)) in
  let int64_of_num n =
    let v = ref 0L in
    String.iter (fun c -> v := Int64.add (Int64.mul !v 10L)
                                (Int64.of_int (Char.code c - 48)))
                (string_of_num n);
    !v in
  let rec eval t =
    try Hashtbl.find memo t with Not_found ->
    let v = match t with
      Comb(Comb(Const("word_xor",_),x),y) -> Int64.logxor (eval x) (eval y)
    | Comb(Comb(Const("word_and",_),x),y) -> Int64.logand (eval x) (eval y)
    | Comb(Comb(Const("word_or",_),x),y) -> Int64.logor (eval x) (eval y)
    | Comb(Const("word_not",_),x) -> Int64.lognot (eval x)
    | Comb(Comb(Const("word_ror",_),x),n) ->
        ror64 (eval x) (dest_small_numeral n)
    | Comb(Comb(Const("word_rol",_),x),n) ->
        ror64 (eval x) ((64 - dest_small_numeral n) mod 64)
    | Comb(Comb(Const("word_subword",_),
                Comb(Comb(Const("word_join",_),x),y)),p)
        when dest_small_numeral(rand p) = 64 ->
        let pos = dest_small_numeral(lhand p) in
        if pos = 0 then eval y else
        Int64.logor (Int64.shift_right_logical (eval y) pos)
                    (Int64.shift_left (eval x) (64 - pos))
    | Comb(Const("word",_),n) when is_numeral n ->
        int64_of_num(dest_numeral n)
    | _ -> atom_val t in
    Hashtbl.add memo t v; v in
  eval;;

(*** Expansion of one round of the specification as an explicit list ***)

let keccak_spec_round_conv =
  REWRITE_CONV[keccak_round] THENC TOP_DEPTH_CONV let_CONV THENC
  ONCE_DEPTH_CONV EL_CONV;;

(*** The abbreviations E_j for the lanes after the first round ***)

let KECCAK_INTRO_ABBREVS_TAC =
  W(fun (asl,w) ->
    let ais = map (fun j -> mk_var("Ai_"^string_of_int j,`:int64`)) (0--24) in
    let tm = mk_comb(mk_comb(`keccak_round`,`EL (2 * i) round_constants`),
                     mk_list(ais,`:int64`)) in
    let specs = dest_list(rhs(concl(keccak_spec_round_conv tm))) in
    let evs = map (fun j -> mk_var("E_"^string_of_int j,`:int64`)) (0--24) in
    MAP_EVERY (fun (e,t) -> ABBREV_TAC(mk_eq(e,t))) (zip evs specs));;

let keccak_abbrevs asl =
  mapfilter (fun (_,th) ->
    let c = concl th in
    let v = rhs c in
    if is_var v && String.length (fst(dest_var v)) > 2 &&
       String.sub (fst(dest_var v)) 0 2 = "E_"
    then (v,lhs c) else failwith "") asl;;

(*** After a step, replace any value that is a lane of the first round ***)

let KECCAK_ABBREV_STEP_TAC =
  let int64_ty = `:int64` in
  W(fun (asl,w) ->
    let s = rand w in
    let evals = map (fun (e,sp) -> (eval64 sp,(e,sp))) (keccak_abbrevs asl) in
    let cands = mapfilter (fun (_,th) ->
       let c = concl th in
       if is_eq c && is_comb(lhs c) && rand(lhs c) = s &&
          type_of(rhs c) = int64_ty && not(is_var(rhs c))
       then let (e,sp) = assoc (eval64(rhs c)) evals in (c,e,sp)
       else failwith "") asl in
    MAP_EVERY (fun (c,e,sp) ->
       let eqth = TRANS (prove(mk_eq(rhs c,sp),KECCAK_BITBLAST_TAC))
                        (ASSUME(mk_eq(sp,e))) in
       FIRST_X_ASSUM(fun th -> if concl th = c then ASSUME_TAC(TRANS th eqth)
                               else failwith "")) cands);;

(*** The final check of the lanes, now in terms of the E_j ***)

let KECCAK_SECOND_ROUND_TAC =
  CONV_TAC(RAND_CONV(REWRITE_CONV
   [ARITH_RULE `2 * (i + 1) = (2 * i + 1) + 1`; keccak])) THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && is_list(lhs(concl th))
    then CONV_TAC(RAND_CONV(REWRITE_CONV[GSYM th]))
    else failwith "") THEN
  CONV_TAC(RAND_CONV(RAND_CONV keccak_spec_round_conv)) THEN
  W(fun (asl,w) ->
    REWRITE_TAC(map (fun (e,sp) -> ASSUME(mk_eq(sp,e)))
                    (keccak_abbrevs asl))) THEN
  CONV_TAC(RAND_CONV keccak_spec_round_conv) THEN
  REWRITE_TAC[CONS_11] THEN REPEAT CONJ_TAC THEN KECCAK_BITBLAST_TAC;;



(* ------------------------------------------------------------------------- *)
(* The invariant of the loop, for i iterations done, i.e. 2 * i rounds. The  *)
(* lanes in row-major order are in the registers and stack slots where the   *)
(* code keeps them at the head of the loop, which are those from which it   *)
(* stores them back after the loop. The stackpointer after                   *)
(* REPEAT_GEN_AND_OFFSET_STACKPTR_TAC is the lowest address of the 288 bytes *)
(* that the code uses: the six saved registers are at stackpointer + 240 to  *)
(* + 280, the pointer to the state at + 216 and the counter (the round       *)
(* index minus two, which indexes the table of round constants) at + 144,    *)
(* and RSP is at + 128, so that the red zone reaches down to stackpointer.   *)
(* ------------------------------------------------------------------------- *)

let keccak_lanes_str =
 "[read R11 s;
   read (memory :> bytes64(word_add stackpointer (word 128))) s;
   read (memory :> bytes64(word_add stackpointer (word 88))) s;
   read R12 s;
   read (memory :> bytes64(word_add stackpointer (word 16))) s;
   read (memory :> bytes64(word_add stackpointer (word 136))) s;
   read (memory :> bytes64(word_add stackpointer (word 48))) s;
   read (memory :> bytes64(word_add stackpointer (word 104))) s;
   read (memory :> bytes64(word_add stackpointer (word 96))) s;
   read (memory :> bytes64(word_add stackpointer (word 24))) s;
   read (memory :> bytes64(word_add stackpointer (word 32))) s;
   read (memory :> bytes64(word_add stackpointer (word 80))) s;
   read R14 s;
   read (memory :> bytes64(word_add stackpointer (word 56))) s;
   read (memory :> bytes64 stackpointer) s;
   read (memory :> bytes64(word_add stackpointer (word 72))) s;
   read RAX s;
   read (memory :> bytes64(word_add stackpointer (word 40))) s;
   read R8 s;
   read (memory :> bytes64(word_add stackpointer (word 8))) s;
   read R9 s;
   read (memory :> bytes64(word_add stackpointer (word 64))) s;
   read R10 s;
   read RSI s;
   read RBP s]";;

let keccak_inv_cs = parse_term ("\\i s.
   read RSP s = word_add stackpointer (word 128) /\\
   read (memory :> bytes64(word_add stackpointer (word 288))) s =
   returnaddress /\\
   read (memory :> bytes64(word_add stackpointer (word 280))) s = rbp_init /\\
   read (memory :> bytes64(word_add stackpointer (word 272))) s = r15_init /\\
   read (memory :> bytes64(word_add stackpointer (word 264))) s = r14_init /\\
   read (memory :> bytes64(word_add stackpointer (word 256))) s = r13_init /\\
   read (memory :> bytes64(word_add stackpointer (word 248))) s = r12_init /\\
   read (memory :> bytes64(word_add stackpointer (word 240))) s = rbx_init /\\
   read (memory :> bytes64(word_add stackpointer (word 216))) s = a /\\
   read (memory :> bytes64(word_add stackpointer (word 144))) s =
   word_sub (word(2 * i)) (word 2) /\\
   " ^ keccak_lanes_str ^ " = keccak (2 * i) A");;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety.                             *)
(* ------------------------------------------------------------------------- *)

let PERMUTE_INTRO_TAC =
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
     APPEND (f_ev_epil a pc stackpointer returnaddress)
      (APPEND
        (ENUMERATEL 12
          (\i. f_ev_loop a pc stackpointer returnaddress i))
        (f_ev_prol a pc stackpointer returnaddress))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES; fst PERM_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun (n,c) -> ENSURES_PRESERVED_TAC n c)
   [("rbx_init",`RBX`); ("rbp_init",`RBP`); ("r12_init",`R12`);
    ("r13_init",`R13`); ("r14_init",`R14`); ("r15_init",`R15`)];;

(* ------------------------------------------------------------------------- *)
(* Initialization: the 25 lanes are loaded and the counter is set.           *)
(* ------------------------------------------------------------------------- *)

let PERMUTE_INIT_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  BIGNUM_DIGITIZE_TAC "A_" `read (memory :> bytes (a,8 * 25)) s0` THEN
  FIRST_ASSUM(MP_TAC o CONV_RULE(LAND_CONV WORDLIST_FROM_MEMORY_CONV)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  X86_STEPS_TAC PERM_EXEC (1--51) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[keccak; MULT_CLAUSES; WORD_ADD_0; LT_REFL] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The loads of the round constants. The code addresses the constant of      *)
(* round 2 * i as table + 8 * c + 16, and that of round 2 * i + 1 as         *)
(* table + 8 * c + 24, with the table address in a register and the counter  *)
(* c = 2 * i - 2 (as a 64-bit word, so -2 for i = 0) in RDX or RAX. The      *)
(* simulation shows the address with val(c), and can only read the table at  *)
(* the initial state if it knows that the address is outside the stack frame *)
(* and does not wrap, so the proof gives it these facts, and the counter and *)
(* table address in the forms of the simulation.                             *)
(* ------------------------------------------------------------------------- *)

let PERM_CTR_LEMMA = prove
 (`!i. i < 12
       ==> word(8 * val(word_sub (word(2 * i)) (word 2):int64) + 16):int64 =
           word(16 * i) /\
           word(8 * val(word_sub (word(2 * i)) (word 2):int64) + 24):int64 =
           word(16 * i + 8)`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV);;

let PERM_RC_FACT = prove
 (`!pc j (s:x86state).
     bytes_loaded s (word pc)
       mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\ j < 24
     ==> read (memory :> bytes64(word_add (word(pc + 152544)) (word(8 * j)))) s =
         EL j round_constants`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`word(pc + 152544):int64`; `round_constants`; `24`; `j:num`;
                 `s:x86state`] READ_MEMORY_BYTES64_NUM_OF_WORDLIST) THEN
  ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[LENGTH_ROUND_CONSTANTS] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`s:x86state`; `pc:num`] KECCAK_RC_IMAGE_VALUE) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[]]);;

let PERM_VALPC = prove
 (`pc + 153952 <= 2 EXP 64
   ==> val(word (pc + 141557):int64) = pc + 141557 /\
       val(word (pc + 142603):int64) = pc + 142603`,
  STRIP_TAC THEN CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
  REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC);;

(*** The address of a constant is within the table and so does not overlap
     the stack frame ***)

let PERM_RC_NONOV = prove
 (`!pc i (stk:int64) off.
     i < 12 /\ pc + 153952 <= 2 EXP 64 /\
     (off = 16 \/ off = 24) /\
     nonoverlapping_modulo (2 EXP 64) (val stk,288) (pc,153952)
     ==> nonoverlapping_modulo (2 EXP 64)
           (val(word_add (word (pc + 152544))
                  (word (8 * val(word_sub (word (2 * i)) (word 2):int64) + off))
                :int64),8) (val stk,288) /\
         nonoverlapping_modulo (2 EXP 64) (val stk,288)
           (val(word_add (word (pc + 152544))
                  (word (8 * val(word_sub (word (2 * i)) (word 2):int64) + off))
                :int64),8)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THEN
  ASM_REWRITE_TAC[MATCH_MP PERM_CTR_LEMMA (ASSUME `i < 12`)] THEN
  REWRITE_TAC[GSYM WORD_ADD] THENL
   [SUBGOAL_THEN `val(word((pc + 152544) + 16 * i):int64) = (pc + 152544) + 16 * i`
    SUBST1_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `contained_modulo (2 EXP 64) ((pc + 152544) + 16 * i,8) (pc,153952)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CONTAINED_MODULO_SIMPLE THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`2 EXP 64`; `pc:num`; `153952`; `val(stk:int64)`; `288`;
                   `(pc + 152544) + 16 * i`; `8`; `val(stk:int64)`; `288`]
                  NONOVERLAPPING_MODULO_SUBREGIONS) THEN
    ASM_REWRITE_TAC[CONTAINED_MODULO_REFL; LE_REFL] THEN
    ASM_MESON_TAC[NONOVERLAPPING_MODULO_SYM];
    SUBGOAL_THEN `val(word((pc + 152544) + (16 * i + 8)):int64) = (pc + 152544) + (16 * i + 8)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `contained_modulo (2 EXP 64) ((pc + 152544) + (16 * i + 8),8) (pc,153952)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CONTAINED_MODULO_SIMPLE THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`2 EXP 64`; `pc:num`; `153952`; `val(stk:int64)`; `288`;
                   `(pc + 152544) + (16 * i + 8)`; `8`; `val(stk:int64)`; `288`]
                  NONOVERLAPPING_MODULO_SUBREGIONS) THEN
    ASM_REWRITE_TAC[CONTAINED_MODULO_REFL; LE_REFL] THEN
    ASM_MESON_TAC[NONOVERLAPPING_MODULO_SYM]]);;

(*** The facts for the two loads of iteration i ***)

let PERM_RC_ALT_TAC k =
  let kk,dd,oo = if k = 0 then 141557,10987,16 else 142603,9941,24 in
  let idx = if k = 0 then "2 * i" else "2 * i + 1" in
  let t = parse_term(Printf.sprintf
   "read (memory :> bytes64 (word_add (word (pc + 152544)) (word (8 * val (word_sub (word (2 * i)) (word 2):int64) + %d)))) s0 = EL (%s) round_constants" oo idx) in
  let eq2 = parse_term(Printf.sprintf "8 * (%s) = %s" idx
              (if k = 0 then "16 * i" else "16 * i + 8")) in
  SUBGOAL_THEN t ASSUME_TAC THENL
   [REWRITE_TAC[MATCH_MP PERM_CTR_LEMMA (ASSUME `i < 12`)] THEN
    MP_TAC(SPECL [`pc:num`; parse_term idx; `s0:x86state`] PERM_RC_FACT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE eq2] THEN
    DISCH_THEN ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`pc:num`; `i:num`; `stackpointer:int64`;
                parse_term(string_of_int oo)] PERM_RC_NONOV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN ASSUME_TAC(CONJUNCT2 th));;

(*** After the LEA that forms the address of the table (at steps 82 and 373
     of the body) its register holds word(pc + 152544) in the simulation's
     form, with val(word(pc + K)) for pc + K ***)

let PERM_LEA_NORM_TAC =
  FIRST_ASSUM(fun pth ->
    if concl pth = `pc + 153952 <= 2 EXP 64`
    then RULE_ASSUM_TAC(REWRITE_RULE[MP PERM_VALPC pth;
          ARITH_RULE `(pc + 141557) + 10987 = pc + 152544`;
          ARITH_RULE `(pc + 142603) + 9941 = pc + 152544`])
    else failwith "PERM_LEA_NORM_TAC");;

(* ------------------------------------------------------------------------- *)
(* The loop body, which does two rounds: 509 steps, each followed by the     *)
(* replacement of the lanes of the first round by variables.                 *)
(* ------------------------------------------------------------------------- *)

let PERMUTE_BODY1_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  GHOST_STATELIST_TAC THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  PERM_RC_ALT_TAC 0 THEN PERM_RC_ALT_TAC 1 THEN
  KECCAK_INTRO_ABBREVS_TAC THEN
  MAP_EVERY (fun n ->
    X86_STEPS_TAC PERM_EXEC [n] THEN
    (if n = 82 || n = 373 then PERM_LEA_NORM_TAC else ALL_TAC) THEN
    KECCAK_ABBREV_STEP_TAC) (1--509);;

(* ------------------------------------------------------------------------- *)
(* The end of an iteration: the loop test, the counter, the lanes after two  *)
(* more rounds, and the events. The event of the load of a round constant   *)
(* has the address in the form of the simulation, which the check that the   *)
(* access is within the table needs in the form table + 16 * i + k.          *)
(* ------------------------------------------------------------------------- *)

(*** Run a tactic with the loads of round constants in the events written
     with the address table + 16 * i + k ***)

let PERM_NORMALIZE_ADDR_TAC (tac:tactic) : tactic = fun g ->
  memaccess_inbounds_normalize_tac :=
   (FIRST_ASSUM(fun th ->
      if concl th = `i < 12`
      then REWRITE_TAC[MATCH_MP PERM_CTR_LEMMA th] else failwith "")
    ORELSE ALL_TAC);
  let r = try tac g with e -> (memaccess_inbounds_normalize_tac := ALL_TAC;
                               raise e) in
  memaccess_inbounds_normalize_tac := ALL_TAC;
  r;;

let PERMUTE_BODY2_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s509" THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `val(word_add (word_sub (word (2*i)) (word 2)) (word 2):int64) = 2*i`
     SUBST1_TAC THENL
     [REWRITE_TAC[WORD_RULE `word_add (word_sub x y) y = x`] THEN
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[ARITH_RULE `2 * i < 22 <=> i + 1 < 12`] THEN
      COND_CASES_TAC THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  CONJ_TAC THENL [KECCAK_SECOND_ROUND_TAC; ALL_TAC] THEN
  PERM_NORMALIZE_ADDR_TAC DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The return: the 25 lanes are stored from the registers and stack slots,   *)
(* the registers are restored.                                               *)
(* ------------------------------------------------------------------------- *)

let PERMUTE_TAIL_TAC =
  REWRITE_TAC[] THEN GHOST_STATELIST_TAC THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  X86_STEPS_TAC PERM_EXEC (1--59) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [CONV_TAC(LAND_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    DISCHARGE_SAFETY_PROPERTY_TAC];;

install_layout (layout_labels [
  "mldsa_keccakf1600_permute", ["loop1",0xf0; "loop1_exit",0x839]]);;

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  PERMUTE_INTRO_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `12` `pc + mldsa_keccakf1600_permute_loop1`
   `pc + mldsa_keccakf1600_permute_loop1_exit` keccak_inv_cs THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    PERMUTE_INIT_TAC;
    PERMUTE_BODY1_TAC THEN PERMUTE_BODY2_TAC;
    PERMUTE_TAIL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The same for the state as a 1600-bit word, and correctness and constant   *)
(* time and memory safety alone.                                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600 =
  prove
 (MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600_STMT,
  MP_TAC
    MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`;
    `wordlist_of_num 25 (val(S:1600 word)):int64 list`;
    `pc:num`; `stackpointer:int64`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_WEAKEN_PREPOST) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[READ_MEMORY_WBYTES_KECCAK] THEN SIMP_TAC[];
    MESON_TAC[KECCAK_F1600_MEMORY]]);;

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_F1600 =
  prove
 (MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_F1600_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600);;

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;
