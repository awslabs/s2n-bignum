(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Centered binomial distribution with eta = 3. This is the code for         *)
(* mlkem_poly_cbd3 from mlkem-native's portable C implementation compiled by *)
(* gcc 12 with -O2 (see mlkem_native/README.md). It is verified in the whole *)
(* image (see mlkem_native_libmlkem_gcc12_O2.ml), where it is at address     *)
(* 0x6420. As for mlkem_poly_cbd2, it saves RBX on the stack, so it is       *)
(* verified directly as a subroutine, with that part of the stack.           *)
(* ========================================================================= *)

needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    6420: push   rbx
    6421: mov    r8,rdi
    6424: xor    r9d,r9d
    6427: mov    rdi,rsi
    642a: nop    WORD PTR [rax+rax*1+0x0]
    6430: movzx  eax,BYTE PTR [rdi+0x1]
    6434: movzx  edx,BYTE PTR [rdi+0x2]
    6438: mov    r10d,r9d
    643b: movzx  ecx,BYTE PTR [rdi]
    643e: shl    edx,0x10
    6441: shl    eax,0x8
    6444: or     eax,edx
    6446: or     eax,ecx
    6448: mov    esi,eax
    644a: mov    edx,eax
    644c: shr    eax,0x2
    644f: shr    esi,1
    6451: and    eax,0x249249
    6456: and    edx,0x249249
    645c: and    esi,0x249249
    6462: add    esi,eax
    6464: add    esi,edx
    6466: xor    edx,edx
    6468: mov    ecx,edx
    646a: mov    eax,esi
    646c: mov    ebx,esi
    646e: mov    r11d,r10d
    6471: shr    eax,cl
    6473: lea    ecx,[rdx+0x3]
    6476: add    edx,0x6
    6479: add    r10d,0x1
    647d: shr    ebx,cl
    647f: and    eax,0x7
    6482: mov    ecx,ebx
    6484: and    ecx,0x7
    6487: sub    eax,ecx
    6489: mov    WORD PTR [r8+r11*2],ax
    648e: cmp    edx,0x18
    6491: jne    6468 <mlkem_poly_cbd3+0x48>
    6493: add    r9d,0x4
    6497: add    rdi,0x3
    649b: cmp    r9d,0x100
    64a2: jne    6430 <mlkem_poly_cbd3+0x10>
    64a4: pop    rbx
    64a5: ret
 ***)

let MLKEM_NATIVE_POLY_CBD3_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x6420,0x64a6];;

(*** The three bytes for four coefficients, as parts of a 24-bit word ***)

let CBD3_BYTES = prove
 (`!a n i s j.
        read (memory :> bytes(a,192)) s = n /\ i < 64 /\ j < 3
        ==> read (memory :> bytes8(word_add a (word(3 * i + j)))) s =
            word_subword (word(n DIV 2 EXP (24 * i)):24 word) (8 * j,8)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o rand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `192`; `n:num`; `3 * i + j`; `s:x86state`]
                READ_MEMORY_BYTES8_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2 EXP 8 = 256`] THEN
  REWRITE_TAC[ARITH_RULE `8 * (3 * i + j) = 24 * i + 8 * j`]);;

(* ------------------------------------------------------------------------- *)
(* Each iteration takes three bytes as a 24-bit word t and adds its groups   *)
(* of three bits. Coefficient j of 4 is computed from the sum shifted right  *)
(* by 6 * j and 6 * j + 3, which depends only on the 6-bit field j of t.     *)
(* Below, the computation on a 6-bit field is checked for all its values and *)
(* related to the bits of the number for the input bytes, as for             *)
(* mlkem_poly_cbd2.                                                          *)
(* ------------------------------------------------------------------------- *)

let SIXBIT_BIT = prove
 (`!n m k. k < 6
           ==> (n DIV 2 EXP (m + k)) MOD 2 =
               (((n DIV 2 EXP m) MOD 64) DIV 2 EXP k) MOD 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
  SPEC_TAC(`n DIV 2 EXP m`,`x:num`) THEN GEN_TAC THEN
  GEN_REWRITE_TAC (BINOP_CONV o RAND_CONV) [GSYM(SPEC `2` EXP_1)] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; ARITH_RULE `64 = 2 EXP 6`;
              MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE `k < 6 ==> MIN 6 (k + 1) = k + 1`]);;

let CBD3_FIELD = prove
 (`!m. m < 64
       ==> word_sub
            (word_zx (word_add (word_add (word_and (word m:6 word) (word 1))
                                         (word_and (word_ushr (word m) 1)
                                                   (word 1)))
                               (word_and (word_ushr (word m) 2) (word 1))))
            (word_zx (word_add (word_add (word_and (word_ushr (word m:6 word)
                                                              3) (word 1))
                                         (word_and (word_ushr (word m) 4)
                                                   (word 1)))
                               (word_ushr (word m) 5))):int16 =
           iword(&(m MOD 2 + (m DIV 2) MOD 2 + (m DIV 4) MOD 2) -
                 &((m DIV 8) MOD 2 + (m DIV 16) MOD 2 + (m DIV 32) MOD 2))`,
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC INT_RED_CONV ORELSEC
                      WORD_RED_CONV)));;

let CBD3_LANE = prove
 (`!n i j w:24 word.
      j < 4 /\ word(n DIV 2 EXP (24 * i)) = w
      ==> let x:6 word = word_subword w (6 * j,6) in
          word_sub
            (word_zx (word_add (word_add (word_and x (word 1))
                                         (word_and (word_ushr x 1) (word 1)))
                               (word_and (word_ushr x 2) (word 1))))
            (word_zx (word_add (word_add (word_and (word_ushr x 3) (word 1))
                                         (word_and (word_ushr x 4) (word 1)))
                               (word_ushr x 5))):int16 =
          iword(&((n DIV 2 EXP (6 * (4 * i + j))) MOD 2 +
                  (n DIV 2 EXP (6 * (4 * i + j) + 1)) MOD 2 +
                  (n DIV 2 EXP (6 * (4 * i + j) + 2)) MOD 2) -
                &((n DIV 2 EXP (6 * (4 * i + j) + 3)) MOD 2 +
                  (n DIV 2 EXP (6 * (4 * i + j) + 4)) MOD 2 +
                  (n DIV 2 EXP (6 * (4 * i + j) + 5)) MOD 2))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN
   `word_subword (word(n DIV 2 EXP (24 * i)):24 word) (6 * j,6):6 word =
    word((n DIV 2 EXP (6 * (4 * i + j))) MOD 64)`
  SUBST1_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o lhand o snd) THEN
    ANTS_TAC THENL
     [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ASM_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN
    REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2 EXP 6 = 64`] THEN
    REWRITE_TAC[ARITH_RULE `24 * i + 6 * j = 6 * (4 * i + j)`];
    ALL_TAC] THEN
  SIMP_TAC[CBD3_FIELD; MOD_LT_EQ; ARITH_EQ] THEN
  SIMP_TAC[SIXBIT_BIT; ARITH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GEN_ALL(CONV_RULE NUM_REDUCE_CONV
   (SPECL [`x:num`; `2`; `32`] MOD_MOD))]);;

(*** Coefficient k of the iteration, from its 16-bit store, with w as given
 *** by tth
 ***)

let CBD3_LANE_RULE k tth th =
  let jt = mk_small_numeral k in
  let lth = CONV_RULE(TOP_DEPTH_CONV let_CONV THENC
                      ONCE_DEPTH_CONV NUM_MULT_CONV THENC
                      REWRITE_CONV[ADD_CLAUSES])
   (MP (SPECL [`n:num`; `i:num`; jt; `w:24 word`] CBD3_LANE)
       (CONJ (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool` jt `4`)))
             tth)) in
  let th1 = CONV_RULE(RAND_CONV(REWRITE_CONV[WORD_VAL_MOD_65536])) th in
  let eq = mk_eq(rand(concl th1),lhs(concl lth)) in
  TRANS th1 (TRANS (BITBLAST_RULE eq) lth);;

(* ------------------------------------------------------------------------- *)
(* The inner loop over the 4 coefficients of an iteration, unrolled in the   *)
(* simulation, as for mlkem_poly_cbd2.                                       *)
(* ------------------------------------------------------------------------- *)

let CBD3_INDEX_TAC k =
  let jt = if k = 0 then `4 * i` else
           mk_binop `(+):num->num->num` `4 * i` (mk_small_numeral k) in
  let wt = mk_comb(`word:num->int64`,jt) in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read R11 s = x`) c then
      MP_TAC th THEN
      SUBGOAL_THEN (mk_eq(rand c,wt)) SUBST1_TAC THENL
       [WORD_SMALL_TAC; DISCH_TAC] THEN
      SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,wt),jt)) ASSUME_TAC THENL
       [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        UNDISCH_TAC `i < 64` THEN ARITH_TAC;
        ALL_TAC]
    else failwith "CBD3_INDEX_TAC");;

let CBD3_STORE_TAC k =
  let jt = if k = 0 then `4 * i` else
           mk_binop `(+):num->num->num` `4 * i` (mk_small_numeral k) in
  let addr = mk_comb(mk_comb(`word_add:int64->int64->int64`,`r:int64`),
                     mk_comb(`word:num->int64`,
                             mk_binop `( * ):num->num->num` `2` jt)) in
  let pat = vsubst [addr,`addr:int64`]
              `read (memory :> bytes16 addr) s = x` in
  W(fun (asl,w) ->
    let tth = snd(find (fun (_,th) ->
      let c = concl th in is_eq c && rand c = `w:24 word` &&
      (try fst(dest_const(rator(lhs c))) = "word" with Failure _ -> false))
      asl) in
    FIRST_X_ASSUM(fun th ->
      if can (term_match [] pat) (concl th)
      then ASSUME_TAC(CBD3_LANE_RULE k tth th)
      else failwith "CBD3_STORE_TAC"));;

let CBD3_INNER_TAC store k =
  (if k = 0 then ALL_TAC else
   X86_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_O2_EXEC
    ((19 + 16 * k)--(22 + 16 * k))) THEN
  CBD3_INDEX_TAC k THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_O2_EXEC
   ((23 + 16 * k)--(34 + 16 * k)) THEN
  (if store then CBD3_STORE_TAC k else ALL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_cbd 3 in common/fips203.ml, coefficient i *)
(* of the result is the number of 1 bits among bits 6 * i to 6 * i + 2 of    *)
(* the 192 bytes as a number n, minus the number among bits 6 * i + 3 to     *)
(* 6 * i + 5, here as a 16-bit integer rather than modulo 3329.              *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_CBD3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!r a n pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        ALL (nonoverlapping (r,512))
            [(word pc,0x82a0); (a,192); (word_sub stackpointer (word 8),16)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 8),16))
            [(word pc,0x82a0); (a,192)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x6420) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,192)) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          iword(&((n DIV 2 EXP (6 * i)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 1)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 2)) MOD 2) -
                                &((n DIV 2 EXP (6 * i + 3)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 4)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 5)) MOD 2)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512);
                         memory :> bytes(word_sub stackpointer (word 8),8)])`,
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `n:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 8 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN

  (*** The outer loop, over groups of three bytes ***)

  ENSURES_WHILE_UP_TAC `64` `pc + 0x6430` `pc + 0x649b`
   `\i s. read R8 s = r /\ read RDI s = word_add a (word(3 * i)) /\
          read R9 s = word(4 * i) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = rbx_init /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s =
          returnaddress /\
          read (memory :> bytes(a,192)) s = n /\
          !j. j < 4 * i
              ==> read(memory :> bytes16(word_add r (word(2 * j)))) s =
                  iword(&((n DIV 2 EXP (6 * j)) MOD 2 +
                          (n DIV 2 EXP (6 * j + 1)) MOD 2 +
                          (n DIV 2 EXP (6 * j + 2)) MOD 2) -
                        &((n DIV 2 EXP (6 * j + 3)) MOD 2 +
                          (n DIV 2 EXP (6 * j + 4)) MOD 2 +
                          (n DIV 2 EXP (6 * j + 5)) MOD 2))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, saving RBX ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_O2_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0];

    (*** The loop body, for three bytes and four coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun j ->
      MP_TAC(REWRITE_RULE[ADD_CLAUSES]
       (CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)
         (SPECL [`a:int64`; `n:num`; `i:num`; `s0:x86state`;
                 mk_small_numeral j] CBD3_BYTES))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC) (0--2) THEN
    ABBREV_TAC `w:24 word = word(n DIV 2 EXP (24 * i))` THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_O2_EXEC (1--22) THEN
    MAP_EVERY (CBD3_INNER_TAC true) (0--3) THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_O2_EXEC (83--84) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `3 * (i + 1) = 3 * i + 3`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    CONJ_TAC THENL [WORD_SMALL_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE
     `j < 4 * (i + 1) <=>
      j < 4 * i \/ j = 4 * i \/ j = 4 * i + 1 \/ j = 4 * i + 2 \/
      j = 4 * i + 3`] THEN
    REWRITE_TAC[TAUT `(p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)`;
                FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
    ASM_REWRITE_TAC[];

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_O2_EXEC (1--2) THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_zx (word (4 * i):int64)) (word 256):int32) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
                  DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE
       `i < 64 ==> 4 * i < 18446744073709551616`;
                   ARITH_RULE `i < 64 ==> 4 * i < 4294967296`] THEN
      UNDISCH_TAC `i < 64` THEN ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit, restoring RBX, and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_O2_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                       free_in `bytes16` (concl th)))]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly in the same way.   *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let MLKEM_NATIVE_POLY_CBD3_GCC12_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,512))
               [word pc,0x82a0; a,192; word_sub stackpointer (word 8),16] /\
           ALL (nonoverlapping (word_sub stackpointer (word 8),16))
               [word pc,0x82a0; a,192]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x6420) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc
                                (word_sub stackpointer (word 8))
                                returnaddress /\
                         memaccess_inbounds e2
                          [a,192; r,512; word_sub stackpointer (word 8),16]
                          [r,512; word_sub stackpointer (word 8),8]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,512);
                           memory :> bytes(word_sub stackpointer (word 8),
                                           8)])`,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
        (f_ev_epil a r pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 64
            (\i. f_ev_loop a r pc stackpointer returnaddress i))
          (f_ev_prol a r pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `r:int64`; `a:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 8 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_CBD3_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `64` `pc + 0x6430` `pc + 0x64a4`
   `\i s. read R8 s = r /\ read RDI s = word_add a (word(3 * i)) /\
          read R9 s = word(4 * i) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = rbx_init /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s =
          returnaddress` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_CBD3_GCC12_O2_EXEC (1--5) THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_CBD3_GCC12_O2_EXEC (1--2) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_O2_EXEC (1--22) THEN
  MAP_EVERY (CBD3_INNER_TAC false) (0--3) THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_O2_EXEC (83--86) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_zx (word_add (word_zx (word (4 * i):int64):int32) (word 4)):int64 =
    word(4 * (i + 1))`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [WORD_SMALL_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `~(val(word_sub (word_zx (word (4 * (i + 1)):int64)) (word 256):int32) =
      0) <=> i + 1 < 64`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
                DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 64 ==> 4 * (i + 1) < 18446744073709551616`; ARITH_RULE
     `i < 64 ==> 4 * (i + 1) < 4294967296`] THEN
    UNDISCH_TAC `i < 64` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `3 * (i + 1) = 3 * i + 3`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
