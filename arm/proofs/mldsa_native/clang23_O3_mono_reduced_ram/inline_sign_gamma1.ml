(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The inlined poly_uniform_gamma1 of mldsa{44,65,87}_signature_internal in  *)
(* the clang 23 -O3 monolithic reduced-RAM build: the sampling of one        *)
(* polynomial of y from rho'' and a nonce, as clang has inlined it into the  *)
(* product A y (yvec_lazy) and into the computation of z. The code zeroes    *)
(* the SHAKE256 state on the stack, absorbs the 64 bytes of rho'' and the    *)
(* two bytes of the nonce with the padding (straight-line code), squeezes    *)
(* five blocks of 136 bytes into a buffer on the stack (a loop of            *)
(* mldsa_keccakf1600_permute and memcpy), unpacks the first 576 (or 640)     *)
(* bytes of it with polyz_unpack (a vector loop), and zeroes the state and   *)
(* the buffer (stores and memset).                                           *)
(*                                                                           *)
(* The lemmas are stated as the loop lemmas of inline_sign.ml (from a PC to  *)
(* a PC of the caller), for a frame base fr below the stack pointer of the   *)
(* caller (SP = fr + 240, with the 240 bytes of the frame of                 *)
(* mldsa_keccakf1600_permute at fr), so that all the regions have the same   *)
(* base. The offsets of the state and of the buffer from SP are parameters.  *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/keccakf1600_permute_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_pack.ml";;
needs "arm/proofs/utils/mldsa_native_sampling.ml";;
needs "arm/proofs/utils/mldsa_native_libc.ml";;

(* ------------------------------------------------------------------------- *)
(* The squeeze loop: five iterations of the permutation of the state and a   *)
(* memcpy of its first 136 bytes to the buffer (the code of keccak_squeeze   *)
(* with the position at 136 and 680 bytes to go). The registers are          *)
(*   rem   the bytes to go (680 - 136 i), pos the position in the block      *)
(*   (136 at the head of each iteration), off the offset in the buffer       *)
(*   (136 i), chunk the length of the copy and src the address of the state. *)
(* ------------------------------------------------------------------------- *)

let G1_SQ_SUC = prove
 (`!(S:1600 word) i. keccak_f1600 (keccak_squeeze i S) = keccak_squeeze (i + 1) S`,
  REWRITE_TAC[GSYM ADD1; keccak_squeeze]);;

let G1_FIRST136 = prove
 (`!(a:int64) (X:1600 word) s:armstate.
     read (memory :> wbytes a) s = X
     ==> read (memory :> bytes(a,136)) s = val X MOD 2 EXP (8 * 136)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; GSYM READ_BYTES_MOD] THEN
  REWRITE_TAC[READ_BYTES_MOD] THEN CONV_TAC NUM_REDUCE_CONV);;

let G1_NSUM_SUC = prove
 (`!(f:num->num) i. nsum {j | j < i + 1} f = nsum {j | j < i} f + f i`,
  REWRITE_TAC[GSYM ADD1; NSUM_CLAUSES_NUMSEG_LT]);;

let G1_EXTBLK = prove
 (`!(fr:int64) k i (S:1600 word) s:armstate.
     read (memory :> bytes(word_add fr (word k),136 * i)) s =
       nsum {j | j < i} (\j. 2 EXP (8 * 136 * j) *
                             val(keccak_squeeze (j + 1) S) MOD 2 EXP (8 * 136)) /\
     read (memory :> bytes(word_add fr (word (k + 136 * i)),136)) s =
       val(keccak_squeeze (i + 1) S) MOD 2 EXP (8 * 136)
     ==> read (memory :> bytes(word_add fr (word k),136 * (i + 1))) s =
       nsum {j | j < i + 1} (\j. 2 EXP (8 * 136 * j) *
                                 val(keccak_squeeze (j + 1) S) MOD 2 EXP (8 * 136))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[G1_NSUM_SUC; READ_COMPONENT_COMPOSE;
              ARITH_RULE `136 * (i + 1) = 136 * i + 136`; READ_BYTES_COMBINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  SUBGOAL_THEN `word_add (word_add fr (word k)) (word (136 * i)):int64 =
                word_add fr (word (k + 136 * i))` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN
  REWRITE_TAC[ARITH_RULE `8 * 136 * i = 8 * (136 * i)`]);;

let G1_CSEL = prove
 (`!i. i < 5
       ==> (if val(word(680 - 136 * i):int64) < 136 then word(680 - 136 * i):int64
            else word 136) = word 136`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

let G1_ARITH = prove
 (`!i. i < 5
       ==> word_sub (word (680 - 136 * i)) (word 136):int64 =
           word (680 - 136 * (i + 1)) /\
           (val(word_sub (word (680 - 136 * i)) (word 136):int64) = 0 <=>
            ~(i + 1 < 5)) /\
           word_add (word 136) (word (136 * i)):int64 = word (136 * (i + 1)) /\
           word_zx(word_add (word_zx (word 0:int32)) (word_zx (word 136:int64):int32)
                   :int32):int64 = word 136`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

let G1_SQZ_TERM mc loop exit (rem,pos,off,chunk,src) so bo =
  parse_term(Printf.sprintf
   "!mc ea el ev.
      memcpy_full_contract mc ea el ev
      ==> exists f_events.
        forall e (S:1600 word) (fr:int64) pc.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          aligned 16 (word_add fr (word 240)) /\\
          ALLPAIRS nonoverlapping
            [(fr,240); (word_add fr (word %d),200); (word_add fr (word %d),680)]
            [(word pc,libmldsa_size); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
            (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read SP s = word_add fr (word 240) /\\
                  read %s s = word 680 /\\ read %s s = word 136 /\\
                  read %s s = word 0 /\\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                  read (memory :> bytes(ea,el)) s = ev /\\
                  read (memory :> wbytes (word_add fr (word %d))) s = S /\\
                  read events s = e)
            (\\s. read PC s = word (pc + %s) /\\
                  read SP s = word_add fr (word 240) /\\
                  read %s s = word 0 /\\ read %s s = word 136 /\\
                  read %s s = word 680 /\\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                  read (memory :> bytes(ea,el)) s = ev /\\
                  read (memory :> wbytes (word_add fr (word %d))) s =
                    keccak_squeeze 5 S /\\
                  (!j. j < 680
                       ==> read (memory :> bytes8
                                  (word_add (word_add fr (word %d)) (word j))) s =
                           mld_keccak_squeeze_byte 136 S 136 j) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events fr mc pc /\\
                     memaccess_inbounds e2
                      [fr,240; word_add fr (word %d),200;
                       word_add fr (word %d),680;
                       word(pc + got_memcpy),8; ea,el;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [fr,240; word_add fr (word %d),200;
                       word_add fr (word %d),680]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
             MAYCHANGE [%s] ,,
             MAYCHANGE [memory :> bytes(fr,240);
                        memory :> bytes(word_add fr (word %d),200);
                        memory :> bytes(word_add fr (word %d),680)])"
   (240 + so) (240 + bo) mc loop rem pos off (240 + so)
   exit rem pos off (240 + so) (240 + bo)
   (240 + so) (240 + bo) (240 + so) (240 + bo)
   (String.concat "; " (filter (fun r -> let n = int_of_string
       (String.sub r 1 (String.length r - 1)) in n >= 19)
       [rem; pos; off; chunk; src]))
   (240 + so) (240 + bo));;

let G1_SAFETY_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  (CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]) THEN
  REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN
  REPEAT CONJ_TAC THEN DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

let G1_LEFTASSOC_CONV = TRY_CONV(CONS_TO_APPEND_CONV) THENC REWRITE_CONV[APPEND_ASSOC];;

let G1_E2_CORE allowed =
  CONV_TAC(LAND_CONV G1_LEFTASSOC_CONV) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SAFE_UNIFY_REFL_TAC allowed (ref ["f_events_callee"; "f_ev_"]);;

let G1_E2_TAC allowed =
  (CONJ_TAC THENL [CONV_TAC WORD_RULE; G1_E2_CORE allowed]) ORELSE
  G1_E2_CORE allowed;;

let G1_LIBC_CALL_TAC name execth ilist vars n =
  REMOVE_THEN name (fun th ->
    LIBC_CONTRACT_SIM_TAC ~is_safety_thm:true execth th ilist n THENL
     [G1_E2_TAC (ref vars); LABEL_TAC name th]);;

let G1_NOV tm =
  SUBGOAL_THEN tm (fun th -> ASSUME_TAC th THEN
                    ASSUME_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES] th)) THENL
   [NONOVERLAPPING_TAC; ALL_TAC];;

let G1_SQZ_PROVE mc exec loop exit ((rem,pos,off,chunk,src) as regs) so bo =
  let tm = G1_SQZ_TERM mc loop exit regs so bo in
  let st = 240 + so and bf = 240 + bo in
  let stv = parse_term(Printf.sprintf "word_add fr (word %d):int64" st) in
  let bfv = parse_term(Printf.sprintf "word_add fr (word %d):int64" bf) in
  let inv = parse_term(Printf.sprintf
   "\\i s. read SP s = word_add fr (word 240) /\\
          read %s s = word (680 - 136 * i) /\\ read %s s = word 136 /\\
          read %s s = word (136 * i) /\\
          read (memory :> bytes64(word_add (word pc) (word got_memcpy))) s = mc /\\
          read (memory :> bytes(ea,el)) s = ev /\\
          read (memory :> wbytes (word_add fr (word %d))) s = keccak_squeeze i S /\\
          read (memory :> bytes(word_add fr (word %d),136 * i)) s =
            nsum {j | j < i} (\\j. 2 EXP (8 * 136 * j) *
                                  val(keccak_squeeze (j + 1) S) MOD 2 EXP (8 * 136))"
   rem pos off st bf) in
  let allowed = [`fr:int64`; `mc:int64`; `pc:num`; `i:num`] in
  let perm_call name ilist n =
    FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc exec
      name ilist allowed n in
  let sv n = mk_var("s"^string_of_int n,`:armstate`) in
  let body_tac =
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN FULL_INIT_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[APPEND_NIL]) THEN REWRITE_TAC[APPEND_NIL] THEN
    ARM_STEPS_TAC exec (1--7) THEN
    perm_call "H_PERM" [`read X0 s`; `keccak_squeeze i S`; `pc:num`;
                        `read SP s`; `read X30 s`] 8 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[G1_SQ_SUC]) THEN
    FIRST_X_ASSUM(fun th ->
      if (try lhs(concl th) =
              mk_comb(mk_comb(`read:(armstate,1600 word)component->armstate->1600 word`,
                mk_comb(mk_comb(`(:>):(armstate,int64->byte)component->(int64->byte,1600 word)component->(armstate,1600 word)component`,
                  `memory`),mk_comb(`wbytes:int64->(int64->byte,1600 word)component`,stv))),
                sv 8)
          with _ -> false)
      then ASSUME_TAC(MATCH_MP G1_FIRST136 th) THEN
           ASSUME_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600] th)
      else NO_TAC) THEN
    ARM_STEPS_TAC exec (9--19) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `i:num` G1_CSEL) (ASSUME `i < 5`)]) THEN
    LIBC_PLT_TAC exec 19 THEN
    MAP_EVERY G1_NOV
     [mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,
        mk_pair(mk_comb(mk_comb(`word_add:int64->int64->int64`,bfv),
                        `word(136 * i):int64`),`136`)),mk_pair(stv,`200`));
      mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,
        mk_pair(mk_comb(mk_comb(`word_add:int64->int64->int64`,bfv),
                        `word(136 * i):int64`),`136`)),
        `(word_add (word pc) (word got_memcpy):int64,8)`)] THEN
    G1_LIBC_CALL_TAC "H_MEMCPY" exec
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
       `val(keccak_squeeze (i + 1) S) MOD 2 EXP (8 * 136)`; `read X30 s`]
      allowed 24 THEN
    ARM_STEPS_TAC exec (25--28) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `i:num` G1_ARITH) (ASSUME `i < 5`)]) THEN
    REWRITE_TAC[MP (SPEC `i:num` G1_ARITH) (ASSUME `i < 5`)] THEN
    ASM_CASES_TAC `i + 1 < 5` THEN ASM_REWRITE_TAC[READ_MEMORY_WBYTES_1600] THEN
    REPEAT CONJ_TAC THEN
    FIRST [MP_TAC(SPECL [`fr:int64`; mk_small_numeral bf; `i:num`; `S:1600 word`; sv 28] G1_EXTBLK) THEN
           ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
           REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
           ASM_REWRITE_TAC[] THEN G1_SAFETY_TAC] in
  let exit_tac =
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `136 * 5 = 680`]) THEN
    CONJ_TAC THENL
     [MP_TAC(REWRITE_RULE[ARITH_RULE `136 * 5 = 680`]
        (SPECL [bfv; `136`; `5`; `S:1600 word`; `s0:armstate`]
               MLD_SQUEEZE_BLOCKS_BYTES8)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[ARITH_RULE `0 < 136`]; DISCH_THEN ACCEPT_TAC];
      ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC in
  prove(tm,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC
    (REWRITE_RULE[memcpy_full_contract] th) "H_MEMCPY") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERM" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(fr:int64) (mc:int64) (pc:num).
      APPEND (f_ev_epil fr mc pc)
       (APPEND (ENUMERATEL 5 (\i. if i + 1 < 5 then f_ev_c fr mc pc i
                                  else f_ev_l fr mc pc i))
               (f_ev_prol fr mc pc)):(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `S:1600 word`; `fr:int64`;
                       `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL;
              ALLPAIRS; PAIRWISE] THEN
  DISCH_THEN(fun th -> (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) th THEN
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)
      (REWRITE_RULE[NONOVERLAPPING_CLAUSES; fst exec] th)) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `5` (parse_term("pc + " ^ loop))
    (parse_term("pc + " ^ exit)) inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; CONJUNCT1 ENUMERATEL; CONJUNCT1 APPEND] THEN
    REPEAT CONJ_TAC THEN
    REWRITE_TAC[keccak_squeeze; NSUM_CLAUSES_NUMSEG_LT; READ_COMPONENT_COMPOSE;
                READ_BYTES_TRIVIAL] THEN
    TRY DISCHARGE_SAFETY_PROPERTY_TAC;
    body_tac;
    exit_tac]);;

(* ------------------------------------------------------------------------- *)
(* The absorbing: from the start of the inlined poly_uniform_gamma1 to the   *)
(* head of the squeeze loop (54 instructions): the state at sp + 10192 is    *)
(* zeroed with 128-bit stores, rho'' (64 bytes at rp, copied to the buffer   *)
(* of the input at sp + 10400) is XORed into its first 64 bytes, the nonce   *)
(* nb + j (stored at sp + 10464) into bytes 64 and 65, and the padding bytes *)
(* 0x1F and 0x80 into bytes 66 and 135; the position 136 is stored at       *)
(* sp + 10392. The proof splits the 128-bit zero stores that later byte      *)
(* stores overlap into bytes, and assembles the 200 bytes of the state from  *)
(* the final stores (G1_CHAIN_TAC), each piece by bit-blasting against the   *)
(* state as a 1600-bit word.                                                 *)
(* ------------------------------------------------------------------------- *)

(*** the absorbed state for rate 136, 66 bytes ***)

let G1_ABSORB_VAL = prove
 (`!M. M < 2 EXP 528
       ==> val(mld_keccak_absorb_once 136 0x1F 66 M:1600 word) =
           M + 2 EXP 528 * 31 + 2 EXP 1080 * 128`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[MLD_KECCAK_ABSORB_ONCE] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  REWRITE_TAC[keccak_absorb; WORD_XOR_0; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  SIMP_TAC[MLD_KECCAK_PAD_SHORT; ARITH_RULE `66 + 2 <= 136`; ARITH_RULE `31 < 256`] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1] THEN
  SUBGOAL_THEN `(M + 2 EXP (8 * 66) * (31 + 2 EXP (8 * (136 - 66 - 1)) * 128)) =
                M + 2 EXP 528 * 31 + 2 EXP 1080 * 128` SUBST1_TAC THENL
   [REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM EXP_ADD; ADD_ASSOC] THEN
    CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `(M + 2 EXP 528 * 31 + 2 EXP 1080 * 128) < 2 EXP 1088` ASSUME_TAC THENL
   [UNDISCH_TAC `M < 2 EXP 528` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `8 * 136 = 1088`] THEN ASM_SIMP_TAC[MOD_LT] THEN
  MATCH_MP_TAC MOD_LT THEN FIRST_ASSUM(fun th -> MP_TAC th) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let G1_S_WORD = prove
 (`!M. M < 2 EXP (8 * 66)
       ==> mld_keccak_absorb_once 136 0x1F 66 M =
           word_or (word_zx (word M:528 word):1600 word)
                   (word(2 EXP 528 * 31 + 2 EXP 1080 * 128))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  SUBGOAL_THEN `M < 2 EXP 528` ASSUME_TAC THENL
   [UNDISCH_TAC `M < 2 EXP (8 * 66)` THEN REWRITE_TAC[ARITH_RULE `8 * 66 = 528`];
    ALL_TAC] THEN
  ASM_SIMP_TAC[G1_ABSORB_VAL; ARITH_RULE `8 * 66 = 528`] THEN
  SUBGOAL_THEN `(word_zx (word M:528 word):1600 word) || word (2 EXP 528 * 31 + 2 EXP 1080 * 128) = word_add (word_zx (word M:528 word):1600 word) (word (2 EXP 528 * 31 + 2 EXP 1080 * 128))` SUBST1_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP 528 * 31 + 2 EXP 1080 * 128 < 2 EXP 1600` ASSUME_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `M < 2 EXP 1600` ASSUME_TAC THENL [UNDISCH_TAC `M < 2 EXP 528` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `M + 2 EXP 528 * 31 + 2 EXP 1080 * 128 < 2 EXP 1600` ASSUME_TAC THENL [UNDISCH_TAC `M < 2 EXP 528` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_CONV `dimindex(:1600)`; DIMINDEX_CONV `dimindex(:528)`] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `MIN 528 1600 = 528`] THEN
  SUBGOAL_THEN `M MOD 2 EXP 528 = M` SUBST1_TAC THENL [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `M + a + b = M + (a + b)`]);;

(*** the input as a 528-bit word: rho'' and the nonce ***)

let G1_M_JOIN = prove
 (`!RHO (n:int16). RHO < 2 EXP 512
     ==> (word (RHO + 2 EXP 512 * val n):528 word) = word_join n (word RHO:512 word)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_JOIN; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ASM_SIMP_TAC[MOD_LT] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let G1_M_BOUND = prove
 (`!RHO (n:int16). RHO < 2 EXP 512 ==> RHO + 2 EXP 512 * val n < 2 EXP (8 * 66)`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `n:int16` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_16] THEN UNDISCH_TAC `RHO < 2 EXP 512` THEN ARITH_TAC);;

let G1_RP128 = prove
 (`!(a:int64) x (s:armstate) k.
     read (memory :> bytes(a,64)) s = x /\ k < 4
     ==> read (memory :> bytes128 (word_add a (word(16 * k)))) s =
         word_subword (word x:512 word) (128 * k,128)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; BYTES128_WBYTES; READ_COMPONENT_COMPOSE;
              VAL_READ_WBYTES; DIMINDEX_128; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  MP_TAC(ISPECL [`a:int64`; `64`; `read memory (s:armstate)`] READ_BYTES_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT] THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[ARITH_RULE `MIN 128 128 = 128`] THEN
  REWRITE_TAC[ARITH_RULE `128 * k = 8 * (16 * k)`; ARITH_RULE `2 EXP 128 = 2 EXP (8 * 16)`] THEN
  REWRITE_TAC[READ_BYTES_DIV; READ_BYTES_MOD] THEN
  REWRITE_TAC[ARITH_RULE `340282366920938463463374607431768211456 = 2 EXP (8 * 16)`; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  ASM_ARITH_TAC);;

(*** the four 128-bit facts of rho'' at rp in the state s ***)

let G1_RP_FACTS_TAC s =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes(rp:int64,64)) s0 = RHO`) (concl th)
       && rand(concl th) = `RHO:num` && rand(lhs(concl th)) = s
    then MAP_EVERY (fun k ->
           let th1 = SPECL [`rp:int64`; `RHO:num`; s; mk_small_numeral k] G1_RP128 in
           let th2 = MP th1 (CONJ th (EQT_ELIM(NUM_REDUCE_CONV(mk_binary "<" (mk_small_numeral k,`4`))))) in
           ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC REWRITE_CONV[WORD_ADD_0]) th2)) (0--3)
    else NO_TAC);;

(*** The statement of the absorb part: from the start of the inlined     ***)
(*** poly_uniform_gamma1 to the head of the squeeze loop                  ***)

let G1_A_TERM mc start stop jreg =
  parse_term(Printf.sprintf
   "exists f_events.
      forall e (rp:int64) RHO nb j (sp:int64) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        aligned 16 sp /\\
        ALL (nonoverlapping (word_add sp (word 10192),274))
            [(word pc,libmldsa_size); (rp,64)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read SP s = sp /\\ read X8 s = rp /\\ read X9 s = word nb /\\
                  read %s s = word j /\\ read Q7 s = word 0 /\\
                  read X22 s = word_add sp (word 10192) /\\
                  read X26 s = word 136 /\\
                  read (memory :> bytes(rp,64)) s = RHO /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\
                  read SP s = sp /\\ read X22 s = word 680 /\\
                  read X26 s = word 136 /\\
                  read (memory :> wbytes (word_add sp (word 10192))) s =
                    mld_keccak_absorb_once 136 0x1F 66
                     (RHO + 2 EXP 512 * val(word(nb + j):int16)) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events rp sp pc /\\
                     memaccess_inbounds e2
                      [rp,64; word_add sp (word 10192),274]
                      [word_add sp (word 10192),274]))
             (MAYCHANGE [PC; X8; X9; X22] ,,
              MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6] ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(word_add sp (word 10192),274)])"
   mc start jreg stop);;

let G1_NONCE_TAC s =
  W(fun (asl,w) ->
    let pat = subst [s,`s:armstate`] `read (memory :> bytes16 (word_add sp (word 10464))) s` in
    let th = snd(find (fun (_,th) -> is_eq(concl th) && lhs(concl th) = pat) asl) in
    let v = rhs(concl th) in
    let lem = prove(mk_eq(v,`word(nb + j):int16`),
      REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD] THEN
      CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
      CONV_TAC(DEPTH_CONV NUM_MIN_CONV) THEN
      ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
      CONV_TAC(DEPTH_CONV NUM_MIN_CONV) THEN REWRITE_TAC[]) in
    RULE_ASSUM_TAC(REWRITE_RULE[lem]));;
let G1_PTR_ADD = prove(`!b:int64 n k. word_add (word_add b (word n)) (word k) = word_add b (word (n + k))`, REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC]);;
let G1_UNSPLIT = CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT @ [G1_PTR_ADD; GSYM ADD_ASSOC; WORD_ADD_0];;
(* split the zero 128-bit fact at sp + off in state s into 16 byte facts *)
let G1_ZSPLIT_TAC sname off =
  let s = mk_var(sname,`:armstate`) in
  let tm = subst [s,`s0:armstate`; mk_small_numeral off,`OFF:num`]
    `read (memory :> bytes128 (word_add sp (word OFF))) s0 = word 0:int128` in
  FIRST_ASSUM(fun th ->
    if concl th = tm then
      let th1 = REWRITE_RULE G1_UNSPLIT th in
      let th2 = CONV_RULE(DEPTH_CONV NUM_ADD_CONV) th1 in
      let ths = map (CONV_RULE(DEPTH_CONV(WORD_SIMPLE_SUBWORD_CONV))) (CONJUNCTS th2) in
      MAP_EVERY ASSUME_TAC ths
    else NO_TAC);;
(* a zero fact of sz bytes at sp + k from the byte facts *)
let G1_ZLD_TAC sname sz k =
  let tm = parse_term(Printf.sprintf "read (memory :> bytes%d (word_add sp (word %d))) %s = word 0" (8*sz) k sname) in
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT); el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);
                el 3 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT); el 4 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);
                G1_PTR_ADD; GSYM ADD_ASSOC] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC];;

(*** The state after the absorbing, from its pieces (as PU_CHAIN_TAC of  ***)
(*** arm-A's inline_uniform_main.ml)                                      ***)

let G1_READ_MEMORY_BYTES_EXTEND = prove
 (`!d:int64 j k x s:armstate.
        read (memory :> bytes(d,j)) s = x MOD 2 EXP (8 * j) /\
        read (memory :> bytes(word_add d (word j),k)) s =
        (x DIV 2 EXP (8 * j)) MOD 2 EXP (8 * k)
        ==> read (memory :> bytes(d,j + k)) s = x MOD 2 EXP (8 * (j + k))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; MOD_MULT_MOD] THEN
  ARITH_TAC);;

let G1_B16 = prove(`!a:int64 s:armstate. read (memory :> bytes(a,16)) s = val(read (memory :> bytes128 a) s)`,
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES; DIMINDEX_128] THEN CONV_TAC NUM_REDUCE_CONV);;
let G1_B1 = prove(`!a:int64 s:armstate. read (memory :> bytes(a,1)) s = val(read (memory :> bytes8 a) s)`,
  REWRITE_TAC[READ_MEMORY_BYTES_BYTES8]);;

let G1_PIECE16 = prove
 (`!(S:1600 word) (A:int64) (s:armstate) (V:int128) off.
     read (memory :> bytes128 A) s = V /\ V = word_subword S (8 * off,128)
     ==> read (memory :> bytes(A,16)) s = (val S DIV 2 EXP (8 * off)) MOD 2 EXP 128`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[G1_B16] THEN
  ASM_REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_CONV `dimindex(:128)`; MIN; LE_REFL] THEN
  CONV_TAC NUM_REDUCE_CONV);;
let G1_PIECE8 = prove
 (`!(S:1600 word) (A:int64) (s:armstate) (V:byte) off.
     read (memory :> bytes8 A) s = V /\ V = word_subword S (8 * off,8)
     ==> read (memory :> bytes(A,1)) s = (val S DIV 2 EXP (8 * off)) MOD 2 EXP 8`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[G1_B1] THEN
  ASM_REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_CONV `dimindex(:8)`; MIN; LE_REFL] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let G1_SWJ = `word_or (word_zx (word_join (word(nb + j):int16) (word RHO:512 word):528 word):1600 word)
                      (word(2 EXP 528 * 31 + 2 EXP 1080 * 128))`;;
let G1_NORMC = TRY_CONV(REWRITE_CONV[G1_PTR_ADD]) THENC DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV);;
let G1_NORM = CONV_RULE G1_NORMC;;

(* the piece of length len at offset off from sp + base in state sn *)
let G1_PIECE_THM asl sn base off len =
  let sz,lem = if len = 16 then "bytes128",G1_PIECE16 else "bytes8",G1_PIECE8 in
  let ftm = parse_term(Printf.sprintf "read (memory :> %s (word_add sp (word %d))) %s" sz (base + off) sn) in
  let fact = try snd(find (fun (_,th) -> let c = concl th in is_eq c && lhs c = ftm) asl)
             with Failure _ -> failwith ("G1_PIECE_THM: no fact at " ^ string_of_int off) in
  let v = rhs(concl fact) in
  let a = parse_term(Printf.sprintf "word_add sp (word %d):int64" (base + off)) in
  let s = mk_var(sn,`:armstate`) in
  let inst = SPECL [G1_SWJ; a; s; v; mk_small_numeral off] lem in
  let eqt = snd(dest_conj(fst(dest_imp(concl inst)))) in
  let eqth = prove(eqt, CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST) in
  MP inst (CONJ fact eqth);;

let G1_PIECES =
  [0,16; 16,16; 32,16; 48,16; 64,1; 65,1; 66,1] @ map (fun j -> j,1) (67--79) @
  [80,16; 96,16; 112,16] @ map (fun j -> j,1) (128--143) @
  [144,16; 160,16] @ map (fun j -> j,1) (176--199);;

(* bytes(sp + base,200) = val SWJ MOD 2 EXP (8 * 200) in state sn *)
let G1_CHAIN_TAC sn base =
  W(fun (asl,w) ->
    let s = mk_var(sn,`:armstate`) in
    let d = parse_term(Printf.sprintf "word_add sp (word %d):int64" base) in
    let x = mk_comb(`val:1600 word->num`,G1_SWJ) in
    let cur0 = G1_NORM(prove(
      subst [s,`s:armstate`; x,`x:num`; d,`d:int64`]
       `read (memory :> bytes(d,0)) s = x MOD 2 EXP (8 * 0)`,
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; MULT_CLAUSES; EXP; MOD_1])) in
    let step (cur,j) (off,len) =
      assert (off = j);
      let pth = G1_NORM(G1_PIECE_THM asl sn base off len) in
      let ext = G1_NORM(SPECL [d; mk_small_numeral j; mk_small_numeral len; x; s]
                          G1_READ_MEMORY_BYTES_EXTEND) in
      (MP ext (CONJ cur pth), j + len) in
    let fin,n = rev_itlist (fun p st -> step st p) G1_PIECES (cur0,0) in
    ASSUME_TAC fin);;

let G1_MODLEMMA = prove(`!w:1600 word. val w MOD 2 EXP 1600 = val w`,
  GEN_TAC THEN MATCH_MP_TAC MOD_LT THEN MP_TAC(ISPEC `w:1600 word` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`]);;

let G1_READ_BYTES_BOUND = prove
 (`!a n x s:armstate. read (memory :> bytes(a,n)) s = x ==> x < 2 EXP (8 * n)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND]);;

let G1_A_PROVE mc start stop jreg =
  let exec = INLINE_LOOP_EXEC start stop in
  prove(G1_A_TERM mc start stop jreg,
  CONCRETIZE_F_EVENTS_TAC
   `\(rp:int64) (sp:int64) (pc:num). f_ev_a rp sp pc:(uarch_event)list` THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rp:int64`; `RHO:num`; `nb:num`;
                       `j:num`; `sp:int64`; `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN
  FIRST_ASSUM(MP_TAC o CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o MATCH_MP G1_READ_BYTES_BOUND o
    check (can (term_match [] `read (memory :> bytes(rp:int64,64)) s0 = RHO`) o concl)) THEN
  DISCH_TAC THEN
  G1_RP_FACTS_TAC `s0:armstate` THEN
  ARM_STEPS_TAC exec (1--4) THEN
  G1_NONCE_TAC `s4:armstate` THEN
  ARM_STEPS_TAC exec (5--12) THEN
  G1_ZSPLIT_TAC "s12" 10256 THEN G1_ZSPLIT_TAC "s12" 10320 THEN
  G1_ZSPLIT_TAC "s12" 10368 THEN G1_ZLD_TAC "s12" 2 10256 THEN
  ARM_STEPS_TAC exec (13--52) THEN
  G1_ZSPLIT_TAC "s52" 10380 THEN
  ARM_STEPS_TAC exec (53--54) THEN
  G1_CHAIN_TAC "s54" 10192 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[G1_S_WORD; G1_M_BOUND; G1_M_JOIN] THEN
    REWRITE_TAC[READ_MEMORY_WBYTES_1600] THEN
    FIRST_X_ASSUM(fun th ->
      if can (term_match [] `read (memory :> bytes(word_add sp (word 10192),200)) s54 = x`)
             (concl th)
      then ACCEPT_TAC (REWRITE_RULE[G1_MODLEMMA] th) else NO_TAC);
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The whole inlined poly_uniform_gamma1, from its start to the return of    *)
(* the memset of the buffer: the absorbing (G1_A), the squeeze loop (G1_SQZ), *)
(* the polyz_unpack loop (a lemma of inline_sign_unpackz.ml, given as thz)   *)
(* and the zeroing of the state and the buffer. The polynomial at             *)
(* fp + 9056 = fr + 9296 is mld_poly_uniform_gamma1_17 of rho'' (64 bytes at *)
(* rp) and the nonce nb + j. The events depend on the addresses only.        *)
(* ------------------------------------------------------------------------- *)

(*** The index register jreg keeps j, except x21 (the second instance), ***)
(*** which the squeeze loop uses for the address of the state            ***)

let G1_MAIN_TERM mc start stop jreg =
  parse_term(Printf.sprintf
  "!mf mc ea el ev.
     memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e (rp:int64) RHO nb j (fr:int64) pc.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          aligned 16 (word_add fr (word 240)) /\\
          PAIRWISE nonoverlapping
           [(fr,240); (word_add fr (word 10432),984); (word_add fr (word 9296),1024);
            (word_add fr (word 504),8); (word_add fr (word 528),32)] /\\
          ALLPAIRS nonoverlapping
           [(fr,240); (word_add fr (word 10432),984); (word_add fr (word 9296),1024)]
           [(rp,64); (word pc,libmldsa_size);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\\s. aligned_bytes_loaded s (word pc) %s /\\
                    read PC s = word (pc + %s) /\\
                    read SP s = word_add fr (word 240) /\\
                    read X8 s = rp /\\ read X9 s = word nb /\\ read %s s = word j /\\
                    read Q7 s = word 0 /\\ read X19 s = word 0 /\\
                    read X22 s = word_add fr (word 10432) /\\ read X26 s = word 136 /\\
                    read X23 s = word_add fr (word 9296) /\\
                    read (memory :> bytes64 (word_add fr (word 504))) s =
                      word_add fr (word 10753) /\\
                    read (memory :> bytes128 (word_add fr (word 528))) s =
                      word 0xffffff07ffffff06ffffff05ffffff04 /\\
                    read (memory :> bytes128 (word_add fr (word 544))) s =
                      word 0xffffff03ffffff02ffffff01ffffff00 /\\
                    read (memory :> bytes(rp,64)) s = RHO /\\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                    read (memory :> bytes(ea,el)) s = ev /\\
                    read events s = e)
               (\\s. read PC s = word (pc + %s) /\\
                    read SP s = word_add fr (word 240) /\\
                    read X23 s = word_add fr (word 9296) /\\ %s
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                    read (memory :> bytes(ea,el)) s = ev /\\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add fr (word(9296 + 4 * i))))
                               s = mld_poly_uniform_gamma1_17 RHO (word(nb + j)) i) /\\
                    (exists e2.
                       read events s = APPEND e2 e /\\
                       e2 = f_events rp mf mc pc fr /\\
                       memaccess_inbounds e2
                        [rp,64; fr,240; word_add fr (word 10432),984;
                         word_add fr (word 9296),1024;
                         word_add fr (word 504),8; word_add fr (word 528),32;
                         word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [fr,240; word_add fr (word 10432),984;
                         word_add fr (word 9296),1024]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
                MAYCHANGE [X19; X20; X21; X22; X26] ,,
                MAYCHANGE
                 [memory :> bytes(fr,240);
                  memory :> bytes(word_add fr (word 10432),984);
                  memory :> bytes(word_add fr (word 9296),1024)])"
   mc start jreg stop
   (if jreg = "X21" then "" else Printf.sprintf "read %s s = word j /\\" jreg));;

(* the rest of the main proof *)
let G1_NORM_ASM_TAC =
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(REWRITE_CONV[G1_PTR_ADD]) THENC
                           DEPTH_CONV NUM_ADD_CONV));;

let G1_SQB = `mld_keccak_squeeze_byte 136
               (mld_keccak_absorb_once 136 0x1F 66 (RHO + 2 EXP 512 * val(word(nb + j):int16))) 136`;;

let G1_MAIN_REST_TAC exec call =
  call "H_A" [`rp:int64`; `RHO:num`; `nb:num`; `j:num`; `word_add fr (word 240):int64`; `pc:num`] 1 THEN
  G1_NORM_ASM_TAC THEN
  call "H_SQZ" [`mld_keccak_absorb_once 136 0x1F 66 (RHO + 2 EXP 512 * val(word(nb + j):int16))`;
                `fr:int64`; `pc:num`] 2 THEN
  ARM_STEPS_TAC exec (3--7) THEN
  SUBGOAL_THEN (subst [G1_SQB,`b:num->byte`]
   `!i. i < 576 ==> read (memory :> bytes8 (word_add fr (word (10736 + i)))) s7 =
                    (b:num->byte) i`) ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  call "H_Z" [`word_add fr (word 9296):int64`; `word_add fr (word 10736):int64`; G1_SQB; `pc:num`] 8 THEN
  ARM_STEPS_TAC exec (9--29) THEN LIBC_PLT_TAC exec 29 THEN
  G1_LIBC_CALL_TAC "H_MEMSET" exec
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`]
    [`rp:int64`; `mf:int64`; `mc:int64`; `pc:num`; `fr:int64`] 34 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[mld_poly_uniform_gamma1_17; mld_shake256_stream] THEN
  ASM_REWRITE_TAC[] THEN G1_SAFETY_TAC;;

let G1_EXEC_PLT a b =
  let n s = try int_of_string s with Failure _ -> layout s in
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [(n a, n b); layout_range "plt_memcpy"; layout_range "plt_memset"];;

let G1_MAIN_PROVE mc start stop jreg (tha,thsqz,thz) =
  let exec = G1_EXEC_PLT start stop in
  let allowed = [`rp:int64`; `mf:int64`; `mc:int64`; `pc:num`; `fr:int64`] in
  let call name ilist n = FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
                            exec name ilist allowed n in
  prove(G1_MAIN_TERM mc start stop jreg,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    let ms,mcp = CONJ_PAIR th in
    ASSUME_CALLEE_SAFETY_TAILED_TAC
      (MP (SPECL [`mc:int64`;`ea:int64`;`el:num`;`ev:num`] thsqz) mcp) "H_SQZ" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] ms) "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC tha "H_A" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC thz "H_Z" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(rp:int64) (mf:int64) (mc:int64) (pc:num) (fr:int64). f_ev_main rp mf mc pc fr:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rp:int64`; `RHO:num`; `nb:num`; `j:num`;
                       `fr:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE] THEN
  DISCH_THEN(fun th -> (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) th THEN
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)(REWRITE_RULE[NONOVERLAPPING_CLAUSES; fst exec] th)) THEN
  MAP_EVERY (fun g -> REWRITE_TAC[SPECL [`pc:num`; g] WORD_ADD] THEN
                      RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; g] WORD_ADD]))
    [`got_memset:num`; `got_memcpy:num`] THEN
  FULL_INIT_TAC THEN G1_MAIN_REST_TAC exec call);;

