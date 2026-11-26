(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The Keccak-f1600 permutation: the proof (see                              *)
(* keccakf1600_permute_spec.ml). It is the proof of the same function in the *)
(* gcc12_O2_reduced_ram build, with the code of clang 23: the loop does two  *)
(* rounds, as there, but keeps the lanes in registers and in five stack      *)
(* slots, advances the pointer to the round constants and the counter in     *)
(* registers (spilled and reloaded within the body), and computes the        *)
(* address of the table once, before the loop. As for mlkem-native's clang   *)
(* builds, the proof is directly about the image, with the address rc of the *)
(* table as a variable equal to its address in the image.                    *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/keccakf1600_permute_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa_keccakf1600_permute"];;

(* ------------------------------------------------------------------------- *)
(* Reading the round constants from the table.                               *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES64_NUM_OF_WORDLIST = prove
 (`!a:int64 (l:int64 list) n j s:armstate.
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

let KECCAK_RC_IN_IMAGE =
  let d = layout "rodata_mld_KeccakF_RoundConstants" in
  let l = mk_list(fst(chop_list 192 (snd(chop_list d
            (dest_list(rhs(concl
              mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc)))))),
                  `:byte`) in
  let lth = MLDSA_NATIVE_IMAGE_DATA_RULE (REFL l) d
  and lenth = LENGTH_CONV(mk_comb(`LENGTH:byte list->num`,l))
  and nth = prove
   (mk_eq(mk_comb(`num_of_bytelist`,l),`num_of_wordlist round_constants`),
    REWRITE_TAC[round_constants; num_of_bytelist; num_of_wordlist] THEN
    CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV) in
  prove
   (`!s pc.
        aligned_bytes_loaded s (word pc)
          mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
        ==> read (memory :> bytes(word(pc + rodata_mld_KeccakF_RoundConstants),
                                  192)) s =
            num_of_wordlist round_constants`,
    REPEAT GEN_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP lth) THEN
    REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES; lenth; nth]);;

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
(* Combined correctness, constant-time and memory safety proof, for the      *)
(* whole subroutine since the register saves are mixed up with the main      *)
(* code by the compiler. It is first proved with the address rc of the table *)
(* as a variable, equal to the address in the image, so that the loop is     *)
(* about word rc: the address that the ADRP and ADD compute is replaced by   *)
(* word(rc + 8). The other theorems follow from it.                          *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The lanes in row-major order at the head and the end of the loop ***)

let keccak_lanes_str =
 "[read X7 s; read X14 s;
   read (memory :> bytes64(word_add stackpointer (word 136))) s;
   read X16 s;
   read (memory :> bytes64(word_add stackpointer (word 128))) s;
   read X3 s; read X24 s; read X17 s; read X1 s; read X2 s; read X4 s;
   read X22 s; read X25 s; read X6 s; read X18 s; read X0 s; read X8 s;
   read X5 s; read X10 s; read X27 s; read X21 s; read X15 s; read X19 s;
   read X20 s; read X26 s]";;

let keccak_inv_cs = parse_term ("\\i s.
   read SP s = stackpointer /\\
   read X9 s = word_add (word_add (word rc) (word(16 * i))) (word 8) /\\
   read X12 s = word_add (word(2 * i)) (word 18446744073709551614) /\\
   read (memory :> bytes64(word_add stackpointer (word 8))) s = a /\\
   read (memory :> bytes64(word_add stackpointer (word 144))) s = x29_init /\\
   read (memory :> bytes64(word_add stackpointer (word 152))) s =
   returnaddress /\\
   read (memory :> bytes64(word_add stackpointer (word 160))) s = x28_init /\\
   read (memory :> bytes64(word_add stackpointer (word 168))) s = x27_init /\\
   read (memory :> bytes64(word_add stackpointer (word 176))) s = x26_init /\\
   read (memory :> bytes64(word_add stackpointer (word 184))) s = x25_init /\\
   read (memory :> bytes64(word_add stackpointer (word 192))) s = x24_init /\\
   read (memory :> bytes64(word_add stackpointer (word 200))) s = x23_init /\\
   read (memory :> bytes64(word_add stackpointer (word 208))) s = x22_init /\\
   read (memory :> bytes64(word_add stackpointer (word 216))) s = x21_init /\\
   read (memory :> bytes64(word_add stackpointer (word 224))) s = x20_init /\\
   read (memory :> bytes64(word_add stackpointer (word 232))) s = x19_init /\\
   read (memory :> bytes(word rc,192)) s = num_of_wordlist round_constants /\\
   " ^ keccak_lanes_str ^ " = keccak (2 * i) A");;

let PERMUTE_CS_INTRO_TAC =
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (rc:num) (pc:num) (stackpointer:int64)
     (returnaddress:int64).
     APPEND (f_ev_epil a rc pc stackpointer returnaddress)
      (APPEND
        (ENUMERATEL 12
          (\i. f_ev_loop a rc pc stackpointer returnaddress i))
        (f_ev_prol a rc pc stackpointer returnaddress))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[fst MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_EXEC] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `nonoverlapping (stackpointer:int64,240) (word rc,192)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[WORD_ADD] THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN
  ENSURES_PRESERVED_TAC "x24_init" `X24` THEN
  ENSURES_PRESERVED_TAC "x25_init" `X25` THEN
  ENSURES_PRESERVED_TAC "x26_init" `X26` THEN
  ENSURES_PRESERVED_TAC "x27_init" `X27` THEN
  ENSURES_PRESERVED_TAC "x28_init" `X28` THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29`;;

(*** The prologue, given rcth: rc = pc + rodata_mld_KeccakF_RoundConstants ***)

let PERMUTE_CS_INIT_TAC rcth =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[GSYM rcth] o
              MATCH_MP KECCAK_RC_IN_IMAGE) THEN
  BIGNUM_DIGITIZE_TAC "A_" `read (memory :> bytes (a,8 * 25)) s0` THEN
  FIRST_ASSUM(MP_TAC o CONV_RULE(LAND_CONV WORDLIST_FROM_MEMORY_CONV)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ARM_STEPS_TAC MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_EXEC (1--25) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_EXEC (26--26) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[keccak; MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[rcth; WORD_ADD; MULT_CLAUSES; WORD_ADD_0] THEN
    CONV_TAC WORD_RULE; ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The address of the pair of round constants, from the counter 2 * i ***)

let PERMUTE_CS_ADDR = prove
 (`!rc:num i:num.
     word_add (word_add (word rc) (word(16 * i + 8))) (word 18446744073709551608):int64 =
     word_add (word rc) (word(16 * i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_ADD] THEN
  SPEC_TAC(`word(16 * i):int64`,`x:int64`) THEN
  SPEC_TAC(`word rc:int64`,`y:int64`) THEN BITBLAST_TAC);;

let PERMUTE_CS_CTR = prove
 (`!i:num. word_add (word_add (word(2 * i)) (word 18446744073709551614))
                    (word 2):int64 = word(2 * i)`,
  GEN_TAC THEN SPEC_TAC(`word(2 * i):int64`,`x:int64`) THEN BITBLAST_TAC);;

let PERMUTE_CS_NEST = prove
 (`!rc:num i:num.
     word_add (word_add (word rc) (word(16 * i))) (word 8):int64 =
     word_add (word rc) (word(16 * i + 8))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_ADD] THEN
  SPEC_TAC(`word(16 * i):int64`,`x:int64`) THEN
  SPEC_TAC(`word rc:int64`,`y:int64`) THEN BITBLAST_TAC);;

let PERMUTE_CS_BODY1_TAC_N rcth nmax =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  GHOST_STATELIST_TAC THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  MP_TAC(ISPECL [`word rc:int64`; `round_constants`; `24`; `2 * i + 1`;
                 `s0:armstate`] READ_MEMORY_BYTES64_NUM_OF_WORDLIST) THEN
  MP_TAC(ISPECL [`word rc:int64`; `round_constants`; `24`; `2 * i`;
                 `s0:armstate`] READ_MEMORY_BYTES64_NUM_OF_WORDLIST) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC[LENGTH_ROUND_CONSTANTS] THEN
  ASM_SIMP_TAC[ARITH_RULE `i < 12 ==> 2 * i < 24 /\ 2 * i + 1 < 24`] THEN
  REWRITE_TAC[ARITH_RULE
   `8 * (2 * i) = 16 * i /\ 8 * (2 * i + 1) = 16 * i + 8`] THEN
  REPEAT DISCH_TAC THEN
  (*** The second constant is loaded by ldp x26, x9, [x9, #-8] from the  ***)
  (*** address that the step leaves as the nested sum below: the fact   ***)
  (*** about it, in that form, so that the load is resolved.             ***)
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes64 (word_add (word rc) (word (16 * i + 8)))) s0 = x`)
         (concl th)
    then ASSUME_TAC(ONCE_REWRITE_RULE[GSYM(SPECL [`rc:num`; `i:num`]
                                            PERMUTE_CS_NEST)] th)
    else failwith "") THEN
  KECCAK_INTRO_ABBREVS_TAC THEN
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_EXEC [n] THEN
    KECCAK_ABBREV_STEP_TAC) (1--nmax);;

let PERMUTE_CS_BODY1_TAC rcth = PERMUTE_CS_BODY1_TAC_N rcth 296;;

let PERMUTE_CS_TEST = prove
 (`!i. i < 12 ==> (val(word (2 * i):int64) < 22 <=> i + 1 < 12)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word (2 * i):int64) = 2 * i` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

(*** The conjuncts about the pointer and the counter, proved outside the ***)
(*** context (BITBLAST_TAC uses the assumptions)                         ***)

let PERMUTE_CS_X9 = prove
 (`!rc:num i:num.
     word_add (word_add (word rc) (word(16 * i))) (word 24):int64 =
     word_add (word_add (word rc) (word(16 * (i + 1)))) (word 8)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`; WORD_ADD] THEN
  SPEC_TAC(`word(16 * i):int64`,`x:int64`) THEN
  SPEC_TAC(`word rc:int64`,`y:int64`) THEN BITBLAST_TAC);;

let PERMUTE_CS_X12 = prove
 (`!i:num. word(2 * i):int64 =
           word_add (word(2 * (i + 1))) (word 18446744073709551614)`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `2 * (i + 1) = 2 * i + 2`; WORD_ADD] THEN
  SPEC_TAC(`word(2 * i):int64`,`x:int64`) THEN BITBLAST_TAC);;

let PERMUTE_CS_BODY2_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s296" THEN
  REWRITE_TAC[PERMUTE_CS_CTR] THEN
  REWRITE_TAC[MP (SPEC `i:num` PERMUTE_CS_TEST) (ASSUME `i < 12`)] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_ACCEPT_TAC PERMUTE_CS_X9; ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_ACCEPT_TAC PERMUTE_CS_X12; ALL_TAC] THEN
  CONJ_TAC THENL [KECCAK_SECOND_ROUND_TAC; ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let PERMUTE_CS_TAIL_TAC =
  REWRITE_TAC[] THEN GHOST_STATELIST_TAC THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_EXEC (1--44) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [CONV_TAC(LAND_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_RC_STMT =
  `exists f_events.
     forall e a rc A pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        rc = pc + rodata_mld_KeccakF_RoundConstants /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 240),240))
            [word pc,libmldsa_size; a,200] /\
        nonoverlapping (a,200) (word pc,libmldsa_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read PC s = word (pc + mldsa_keccakf1600_permute) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  wordlist_from_memory(a,25) s = A /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  wordlist_from_memory(a,25) s = keccak 24 A /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a rc pc (word_sub stackpointer (word 240))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [a,200; word_sub stackpointer (word 240),240;
                       word rc,192]
                      [a,200; word_sub stackpointer (word 240),240]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(a,200);
                memory :> bytes(word_sub stackpointer (word 240),240)])`;;

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_RC = prove
 (MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_RC_STMT,
  PERMUTE_CS_INTRO_TAC THEN
  FIRST_X_ASSUM(fun rcth ->
    if concl rcth = `rc = pc + rodata_mld_KeccakF_RoundConstants`
    then
      ENSURES_EVENTS_WHILE_UP2_TAC `12` `pc + mldsa_keccakf1600_permute_loop1`
       `pc + mldsa_keccakf1600_permute_loop1_exit`
       keccak_inv_cs THEN
      REPEAT CONJ_TAC THENL
       [ARITH_TAC;
        PERMUTE_CS_INIT_TAC rcth;
        PERMUTE_CS_BODY1_TAC rcth THEN PERMUTE_CS_BODY2_TAC;
        PERMUTE_CS_TAIL_TAC]
    else NO_TAC));;

(* ------------------------------------------------------------------------- *)
(* The theorems for the code in the image: the combined one, with the table  *)
(* at its address in the image, and from it those of correctness, of         *)
(* constant time and memory safety, and for the state as a 1600-bit word.    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  X_CHOOSE_TAC
   `f:int64->num->num->int64->int64->(uarch_event)list`
   MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_RC THEN
  EXISTS_TAC
   `\(a:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      (f:int64->num->num->int64->int64->(uarch_event)list)
      a (pc + rodata_mld_KeccakF_RoundConstants) pc stackpointer
      returnaddress` THEN
  REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`;
    `pc + rodata_mld_KeccakF_RoundConstants`; `A:int64 list`; `pc:num`;
    `stackpointer:int64`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[]);;

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600 =
  prove
 (MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600_STMT,
  MP_TAC MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL THEN
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

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_F1600 =
  prove
 (MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_F1600_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600);;
