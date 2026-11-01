(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a polynomial from bytes, 12 bits per coefficient.            *)
(* This is the code for mlkem_poly_frombytes from mlkem-native's portable C  *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md).  *)
(* It is verified in the whole image (see                                    *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x31c0. As in  *)
(* mlkem_decode in common/fips203.ml, the bytes are given as a number n,     *)
(* with coefficient i being bits 12 * i to 12 * i + 11 of n.                 *)
(* ========================================================================= *)

needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    31c0: lea    r9,[rsi+0x180]
    31c7: nop    WORD PTR [rax+rax*1+0x0]
    31d0: movzx  eax,BYTE PTR [rsi+0x1]
    31d4: movzx  edx,BYTE PTR [rsi+0x2]
    31d8: add    rsi,0x3
    31dc: add    rdi,0x4
    31e0: movzx  r8d,BYTE PTR [rsi-0x3]
    31e5: mov    ecx,eax
    31e7: shr    al,0x4
    31ea: shl    ecx,0x8
    31ed: movzx  eax,al
    31f0: shl    edx,0x4
    31f3: and    cx,0xf00
    31f8: or     eax,edx
    31fa: or     ecx,r8d
    31fd: mov    WORD PTR [rdi-0x2],ax
    3201: mov    WORD PTR [rdi-0x4],cx
    3205: cmp    r9,rsi
    3208: jne    31d0 <mlkem_poly_frombytes+0x10>
    320a: ret
 ***)

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x31c0,0x320b];;

(* ------------------------------------------------------------------------- *)
(* The two coefficients from three bytes.                                    *)
(* ------------------------------------------------------------------------- *)

let FROMBYTES_LANES = prove
 (`!n i.
     word_zx(word_join
              (word_subword (word((n DIV 2 EXP (24 * i + 8)) MOD 256):byte)
                            (0,4):4 word)
              (word((n DIV 2 EXP (24 * i)) MOD 256):byte):12 word):int16 =
     word((n DIV 2 EXP (24 * i)) MOD 4096) /\
     word_zx(word_join
              (word((n DIV 2 EXP (24 * i + 16)) MOD 256):byte)
              (word_subword (word((n DIV 2 EXP (24 * i + 8)) MOD 256):byte)
                            (4,4):4 word):12 word):int16 =
     word((n DIV 2 EXP (24 * i + 12)) MOD 4096)`,
  let rule = GEN_ALL o CONV_RULE NUM_REDUCE_CONV o SPEC_ALL in
  let l1 = rule(SPECL [`m:num`; `16`; `16`] MOD_MOD)
  and l2 = rule(GSYM(SPECL [`m:num`; `16`; `16`] DIV_MOD))
  and l3 = rule(SPECL [`m:num`; `256`; `16`] DIV_DIV)
  and l4 = rule(GSYM(SPECL [`m:num`; `4096`; `16`] DIV_DIV))
  and l5 = rule(GSYM(SPECL [`m:num`; `256`; `16`] MOD_MULT_MOD))
  and l6 = rule(GSYM(SPECL [`m:num`; `16`; `256`] MOD_MULT_MOD)) in
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
  SPEC_TAC(`n DIV 2 EXP (24 * i)`,`m:num`) THEN
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_JOIN;
     VAL_WORD_SUBWORD; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_MOD_REFL; DIV_1; l1; l2; l3] THEN
  REWRITE_TAC[l4] THEN REWRITE_TAC[l5; l6; MOD_MOD_REFL]);;

(* ------------------------------------------------------------------------- *)
(* The address of the first of the two coefficients stored in an iteration   *)
(* is computed as word_add (word_add r (word(4 * i))) (word 2), and it is    *)
(* put in the form word_add r (word(4 * i + 2)) before the second store, so  *)
(* that the simulation knows that they do not overlap.                       *)
(* ------------------------------------------------------------------------- *)

let ADDR_NORM_BYTES16_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (term_match []
         `read (memory :> bytes16 (word_add (word_add a (word m)) (word n)))
               s = v`) (concl th)
    then CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV(REWR_CONV(GSYM WORD_ADD_ASSOC))
                             THENC ONCE_DEPTH_CONV(REWR_CONV(GSYM WORD_ADD))))
                  th
    else th);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_CORRECT = prove
 (`!r a n pc.
    aligned 16 (word pc:int64) /\
    ALL (nonoverlapping (r,512)) [(word pc,0x82a0); (a,384)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
           read RIP s = word (pc + 0x31c0) /\
           C_ARGUMENTS [r; a] s /\
           read (memory :> bytes(a,384)) s = n)
      (\s. read RIP s = word (pc + 0x320a) /\
           !i. i < 256
               ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                   word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(r,512)])`,
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `128` `pc + 0x31d0` `pc + 0x3205`
   `\i s. read RDI s = word_add r (word(4 * i)) /\
          read RSI s = word_add a (word(3 * i)) /\
          read R9 s = word_add a (word 384) /\
          read (memory :> bytes(a,384)) s = n /\
          (!j. j < 2 * i
               ==> read(memory :> bytes16(word_add r (word(2 * j)))) s =
                   word((n DIV 2 EXP (12 * j)) MOD 2 EXP 12))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0];

    (*** The loop body, for three bytes and two coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun k ->
      MP_TAC(SPECL [`a:int64`; `384`; `n:num`; k; `s0:x86state`]
                   READ_MEMORY_BYTES8_OF_NUM) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC])
     [`3 * i`; `3 * i + 1`; `3 * i + 2`] THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC (1--14) THEN
    ADDR_NORM_BYTES16_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC [15] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
      CONV_TAC WORD_RULE;
      REWRITE_TAC[ARITH_RULE `3 * (i + 1) = 3 * i + 3`] THEN
      CONV_TAC WORD_RULE;
      REWRITE_TAC[ARITH_RULE
       `j < 2 * (i + 1) <=> j < 2 * i \/ j = 2 * i \/ j = 2 * i + 1`] THEN
      REWRITE_TAC[TAUT `(p \/ q \/ r ==> s) <=>
                        (p ==> s) /\ (q ==> s) /\ (r ==> s)`;
                  FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `2 * 2 * i = 4 * i`;
                  ARITH_RULE `2 * (2 * i + 1) = 4 * i + 2`] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[GSYM FROMBYTES_LANES] THEN
      REWRITE_TAC[WORD_VAL_MOD_256; WORD_VAL_MOD_65536] THEN
      CONJ_TAC THEN BYTES_BITBLAST_TAC];

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC (1--2) THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_add a (word 384))
                     (word_add a (word (3 * i))):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[WORD_RULE
       `word_sub (word_add a x) (word_add a y):int64 = word_sub x y`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 128 ==> 3 * i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `i < 128` THEN ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC (1--2) THEN
    PTR_DECIDE_RIP_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                       free_in `bytes16` (concl th)))]);;

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!r a n pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\
    ALL (nonoverlapping (r,512))
        [(word pc,0x82a0); (a,384); (stackpointer,8)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
           read RIP s = word (pc + 0x31c0) /\
           read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           C_ARGUMENTS [r; a] s /\
           read (memory :> bytes(a,384)) s = n)
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           !i. i < 256
               ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                   word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12))
      (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(r,512)])`,
  X86_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC
    MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SAFE = time prove
 (`exists f_events.
       forall e r a pc.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,512)) [word pc,0x82a0; a,384]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x31c0) /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = word (pc + 0x320a) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc /\
                         memaccess_inbounds e2 [a,384; r,512] [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,512)])`,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num).
      APPEND
        (f_ev_epil a r pc)
        (APPEND
          (ENUMERATEL 128 (\i. f_ev_loop a r pc i))
          (f_ev_prol a r pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `128` `pc + 0x31d0` `pc + 0x320a`
    `\i s. read RDI s = word_add r (word(4 * i)) /\
           read RSI s = word_add a (word(3 * i)) /\
           read R9 s = word_add a (word 384)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC (1--2) THEN
    REWRITE_TAC[MULT_0; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC (1--0) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC (1--17) THEN
  SUBGOAL_THEN
   `~(val(word_add a (word 384):int64) =
      val(word_add (word_add a (word (3 * i))) (word 3):int64)) <=>
    i + 1 < 128`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_EQ; GSYM WORD_ADD_ASSOC; WORD_ADD_LCANCEL_EQ] THEN
    REWRITE_TAC[GSYM WORD_ADD; WORD_EQ; DIMINDEX_64; CONG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 128 ==> 3 * i + 3 < 18446744073709551616`] THEN
    UNDISCH_TAC `i < 128` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`;
                ARITH_RULE `3 * (i + 1) = 3 * i + 3`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC]) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,512))
               [word pc,0x82a0; a,384; stackpointer,8]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x31c0) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc stackpointer returnaddress /\
                         memaccess_inbounds e2
                          [a,384; r,512; stackpointer,8] [r,512]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,512)])`,
  X86_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC
    MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
