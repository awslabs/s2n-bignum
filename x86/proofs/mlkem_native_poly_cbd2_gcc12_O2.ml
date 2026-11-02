(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling of a polynomial from the centered binomial distribution with     *)
(* eta = 2. This is the code for mlkem_poly_cbd2 from mlkem-native's         *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md). It is verified in the whole image (see           *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x63b0. It     *)
(* saves RBX on the stack, so it is verified directly as a subroutine, with  *)
(* that part of the stack.                                                   *)
(* ========================================================================= *)

needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    63b0: push   rbx
    63b1: mov    r8,rdi
    63b4: mov    r10,rsi
    63b7: xor    r9d,r9d
    63ba: nop    WORD PTR [rax+rax*1+0x0]
    63c0: mov    edi,DWORD PTR [r10+r9*4]
    63c4: lea    esi,[r9*8+0x0]
    63cc: xor    edx,edx
    63ce: mov    eax,edi
    63d0: shr    edi,1
    63d2: and    eax,0x55555555
    63d7: and    edi,0x55555555
    63dd: add    edi,eax
    63df: nop
    63e0: mov    ecx,edx
    63e2: mov    eax,edi
    63e4: mov    ebx,edi
    63e6: mov    r11d,esi
    63e9: shr    eax,cl
    63eb: lea    ecx,[rdx+0x2]
    63ee: add    edx,0x4
    63f1: add    esi,0x1
    63f4: shr    ebx,cl
    63f6: and    eax,0x3
    63f9: mov    ecx,ebx
    63fb: and    ecx,0x3
    63fe: sub    eax,ecx
    6400: mov    WORD PTR [r8+r11*2],ax
    6405: cmp    edx,0x20
    6408: jne    63e0 <mlkem_poly_cbd2+0x30>
    640a: add    r9,0x1
    640e: cmp    r9,0x20
    6412: jne    63c0 <mlkem_poly_cbd2+0x10>
    6414: pop    rbx
    6415: ret
 ***)

let MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x63b0,0x6416];;

(* ------------------------------------------------------------------------- *)
(* Each iteration loads a 32-bit word t of the input and adds its pairs of   *)
(* bits. Coefficient j of 8 is computed from the sum shifted right by 4 * j  *)
(* and 4 * j + 2, which depends only on the 4-bit field j of t. Below, the   *)
(* computation on a 4-bit field is checked for all its values and related    *)
(* to the bits of the number for the input bytes.                            *)
(* ------------------------------------------------------------------------- *)

let NIBBLE_BIT = prove
 (`!n m k. k < 4
           ==> (n DIV 2 EXP (m + k)) MOD 2 =
               (((n DIV 2 EXP m) MOD 16) DIV 2 EXP k) MOD 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
  SPEC_TAC(`n DIV 2 EXP m`,`x:num`) THEN GEN_TAC THEN
  GEN_REWRITE_TAC (BINOP_CONV o RAND_CONV) [GSYM(SPEC `2` EXP_1)] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; ARITH_RULE `16 = 2 EXP 4`;
              MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE `k < 4 ==> MIN 4 (k + 1) = k + 1`]);;

let CBD2_NIBBLE = prove
 (`!m. m < 16
       ==> word_sub
            (word_zx (word_add (word_and (word m:4 word) (word 1))
                               (word_and (word_ushr (word m) 1) (word 1))))
            (word_zx (word_add (word_and (word_ushr (word m:4 word) 2)
                                         (word 1))
                               (word_ushr (word m) 3))):int16 =
           iword(&(m MOD 2 + (m DIV 2) MOD 2) -
                 &((m DIV 4) MOD 2 + (m DIV 8) MOD 2))`,
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC INT_RED_CONV ORELSEC
                      WORD_RED_CONV)));;

let CBD2_LANE = prove
 (`!n i j t:int32.
      j < 8 /\ word((n DIV 2 EXP (32 * i)) MOD 4294967296) = t
      ==> let x:4 word = word_subword t (4 * j,4) in
          word_sub
            (word_zx (word_add (word_and x (word 1))
                               (word_and (word_ushr x 1) (word 1))))
            (word_zx (word_add (word_and (word_ushr x 2) (word 1))
                               (word_ushr x 3))):int16 =
          iword(&((n DIV 2 EXP (4 * (8 * i + j))) MOD 2 +
                  (n DIV 2 EXP (4 * (8 * i + j) + 1)) MOD 2) -
                &((n DIV 2 EXP (4 * (8 * i + j) + 2)) MOD 2 +
                  (n DIV 2 EXP (4 * (8 * i + j) + 3)) MOD 2))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN
   `word_subword (word((n DIV 2 EXP (32 * i)) MOD 4294967296):int32)
                 (4 * j,4):4 word =
    word((n DIV 2 EXP (4 * (8 * i + j))) MOD 16)`
  SUBST1_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o lhand o snd) THEN
    ANTS_TAC THENL
     [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ASM_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN REWRITE_TAC[ARITH_RULE `4294967296 = 2 EXP 32`] THEN
    ASM_SIMP_TAC[DIV_MOD_EXP_LOW; ARITH_RULE `j < 8 ==> 4 * j + 4 <= 32`] THEN
    REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2 EXP 4 = 16`] THEN
    REWRITE_TAC[ARITH_RULE `32 * i + 4 * j = 4 * (8 * i + j)`];
    ALL_TAC] THEN
  SIMP_TAC[CBD2_NIBBLE; MOD_LT_EQ; ARITH_EQ] THEN
  SIMP_TAC[NIBBLE_BIT; ARITH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GEN_ALL(CONV_RULE NUM_REDUCE_CONV
   (SPECL [`x:num`; `2`; `8`] MOD_MOD))]);;

(*** Coefficient k of the iteration, from its 16-bit store, with t as given
 *** by tth
 ***)

let CBD2_LANE_RULE k tth th =
  let jt = mk_small_numeral k in
  let lth = CONV_RULE(TOP_DEPTH_CONV let_CONV THENC
                      ONCE_DEPTH_CONV NUM_MULT_CONV THENC
                      REWRITE_CONV[ADD_CLAUSES])
   (MP (SPECL [`n:num`; `i:num`; jt; `t:int32`] CBD2_LANE)
       (CONJ (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool` jt `8`)))
             tth)) in
  let th1 = CONV_RULE(RAND_CONV(REWRITE_CONV[WORD_VAL_MOD_65536])) th in
  let eq = mk_eq(rand(concl th1),lhs(concl lth)) in
  TRANS th1 (TRANS (BITBLAST_RULE eq) lth);;

(* ------------------------------------------------------------------------- *)
(* The inner loop over the 8 coefficients of an iteration, unrolled in the   *)
(* simulation. R11 is the index of the coefficient, which is tidied up       *)
(* before it is used as a register offset, and CBD2_STORE_TAC puts the fact  *)
(* about the store of the coefficient in its final form.                     *)
(* ------------------------------------------------------------------------- *)

let CBD2_INDEX_TAC k =
  let jt = if k = 0 then `8 * i` else
           mk_binop `(+):num->num->num` `8 * i` (mk_small_numeral k) in
  let wt = mk_comb(`word:num->int64`,jt) in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read R11 s = x`) c then
      let th' = REWRITE_RULE[WORD_SX_64_32; ADD_CLAUSES] th in
      MP_TAC th' THEN
      SUBGOAL_THEN (mk_eq(rand(concl th'),wt)) SUBST1_TAC THENL
       [WORD_SMALL_TAC; DISCH_TAC] THEN
      SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,wt),jt)) ASSUME_TAC THENL
       [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        UNDISCH_TAC `i < 32` THEN ARITH_TAC;
        ALL_TAC]
    else failwith "CBD2_INDEX_TAC");;

let CBD2_STORE_TAC k =
  let jt = if k = 0 then `8 * i` else
           mk_binop `(+):num->num->num` `8 * i` (mk_small_numeral k) in
  let addr = mk_comb(mk_comb(`word_add:int64->int64->int64`,`r:int64`),
                     mk_comb(`word:num->int64`,
                             mk_binop `( * ):num->num->num` `2` jt)) in
  let pat = vsubst [addr,`addr:int64`]
              `read (memory :> bytes16 addr) s = x` in
  W(fun (asl,w) ->
    let tth0 = snd(find (fun (_,th) ->
      let c = concl th in is_eq c && rand c = `t:int32` &&
      (try fst(dest_const(rator(lhs c))) = "word" with Failure _ -> false))
      asl) in
    let tth = CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV
                (REWRITE_CONV[MULT_ASSOC] THENC NUM_REDUCE_CONV))) tth0 in
    FIRST_X_ASSUM(fun th ->
      if can (term_match [] pat) (concl th)
      then ASSUME_TAC(CBD2_LANE_RULE k tth th)
      else failwith "CBD2_STORE_TAC"));;

let CBD2_INNER_TAC store k =
  X86_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC
   ((10 + 16 * k)--(13 + 16 * k)) THEN
  CBD2_INDEX_TAC k THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC
   ((14 + 16 * k)--(25 + 16 * k)) THEN
  (if store then CBD2_STORE_TAC k else ALL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_cbd 2 in common/fips203.ml, coefficient i *)
(* of the result is the number of 1 bits among bits 4 * i and 4 * i + 1 of   *)
(* the 128 bytes as a number n, minus the number among bits 4 * i + 2 and    *)
(* 4 * i + 3, here as a 16-bit integer rather than modulo 3329.              *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_CBD2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!r a n pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        ALL (nonoverlapping (r,512))
            [(word pc,0x82a0); (a,128); (word_sub stackpointer (word 8),16)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 8),16))
            [(word pc,0x82a0); (a,128)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x63b0) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,128)) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          iword(&((n DIV 2 EXP (4 * i)) MOD 2 +
                                  (n DIV 2 EXP (4 * i + 1)) MOD 2) -
                                &((n DIV 2 EXP (4 * i + 2)) MOD 2 +
                                  (n DIV 2 EXP (4 * i + 3)) MOD 2)))
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

  (*** The outer loop, over the 32-bit words of the input ***)

  ENSURES_WHILE_UP_TAC `32` `pc + 0x63c0` `pc + 0x640e`
   `\i s. read R8 s = r /\ read R10 s = a /\ read R9 s = word i /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = rbx_init /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s =
          returnaddress /\
          read (memory :> bytes(a,128)) s = n /\
          !j. j < 8 * i
              ==> read(memory :> bytes16(word_add r (word(2 * j)))) s =
                  iword(&((n DIV 2 EXP (4 * j)) MOD 2 +
                          (n DIV 2 EXP (4 * j + 1)) MOD 2) -
                        &((n DIV 2 EXP (4 * j + 2)) MOD 2 +
                          (n DIV 2 EXP (4 * j + 3)) MOD 2))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, saving RBX ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT];

    (*** The loop body, for one 32-bit word t and 8 coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC(SPECL [`a:int64`; `128`; `n:num`; `4 * i`; `s0:x86state`]
                 READ_MEMORY_BYTES32_OF_NUM) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [UNDISCH_TAC `i < 32` THEN ARITH_TAC; DISCH_TAC] THEN
    VAL_INT64_TAC `i:num` THEN
    ABBREV_TAC `t:int32 = word((n DIV 2 EXP (8 * 4 * i)) MOD 4294967296)` THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC (1--9) THEN
    MAP_EVERY (CBD2_INNER_TAC true) (0--7) THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC [138] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REWRITE_TAC[WORD_ADD]; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE
     `j < 8 * (i + 1) <=>
      j < 8 * i \/ j = 8 * i \/ j = 8 * i + 1 \/ j = 8 * i + 2 \/
      j = 8 * i + 3 \/ j = 8 * i + 4 \/ j = 8 * i + 5 \/ j = 8 * i + 6 \/
      j = 8 * i + 7`] THEN
    REWRITE_TAC[TAUT `(p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)`;
                FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
    ASM_REWRITE_TAC[];

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC (1--2) THEN
    SUBGOAL_THEN `~(val(word_sub (word i) (word 32):int64) = 0)`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 32 ==> i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `i < 32` THEN ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit, restoring RBX, and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                       free_in `bytes16` (concl th)))]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly in the same way.   *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let MLKEM_NATIVE_POLY_CBD2_GCC12_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,512))
               [word pc,0x82a0; a,128; word_sub stackpointer (word 8),16] /\
           ALL (nonoverlapping (word_sub stackpointer (word 8),16))
               [word pc,0x82a0; a,128]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x63b0) /\
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
                          [a,128; r,512; word_sub stackpointer (word 8),16]
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
          (ENUMERATEL 32
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
              fst MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + 0x63c0` `pc + 0x6414`
   `\i s. read R8 s = r /\ read R10 s = a /\ read R9 s = word i /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = rbx_init /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s =
          returnaddress` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC (1--5) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC (1--2) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  VAL_INT64_TAC `i:num` THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC (1--9) THEN
  MAP_EVERY (CBD2_INNER_TAC false) (0--7) THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC (138--140) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `~(val(word_add (word i) (word 18446744073709551585):int64) = 0) <=>
    i + 1 < 32`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    UNDISCH_TAC `i < 32` THEN SPEC_TAC(`i:num`,`i:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[WORD_ADD]; ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
