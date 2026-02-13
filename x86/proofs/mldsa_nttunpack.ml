(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* NTT unpack for ML-DSA: 8x8 transpose within 4 blocks                      *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(**** print_literal_from_elf "x86/mldsa/mldsa_nttunpack.o";;
 ****)

let mldsa_nttunpack_mc = define_assert_from_elf "mldsa_nttunpack_mc" "x86/mldsa/mldsa_nttunpack.o"


let mldsa_nttunpack_tmc = define_trimmed "mldsa_nttunpack_tmc" mldsa_nttunpack_mc;;
let MLDSA_NTTUNPACK_TMC_EXEC = X86_MK_CORE_EXEC_RULE mldsa_nttunpack_tmc;;

(* ------------------------------------------------------------------------- *)
(* Specification: mldsa_nttunpack performs an 8x8 transpose within each of   *)
(* 4 blocks of 64 coefficients, converting from AVX2 lane-interleaved to     *)
(* sequential layout. This is analogous to mlkem_unpack but for int32.       *)
(* ------------------------------------------------------------------------- *)

let nttunpack_order = new_definition
  `nttunpack_order i =
   let block = i DIV 64 in
   let pos = i MOD 64 in
   let lane = pos DIV 8 in
   let offset = pos MOD 8 in
   64 * block + 8 * offset + lane`;;

let nttunpack_unorder = new_definition
  `nttunpack_unorder i =
   let block = i DIV 64 in
   let pos = i MOD 64 in
   let lane = pos MOD 8 in
   let offset = pos DIV 8 in
   64 * block + 8 * lane + offset`;;

let pack_nttunpack = new_definition
  `pack_nttunpack l = list_of_seq (\i. EL (nttunpack_order i) l) 256`;;

let unpack_nttunpack = new_definition
  `unpack_nttunpack l = list_of_seq (\i. EL (nttunpack_unorder i) l) 256`;;

(* ------------------------------------------------------------------------- *)
(* Main correctness theorem                                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NTTUNPACK_CORRECT = prove
  (`!a (l:int32 list) pc.
    aligned 32 a /\
    nonoverlapping (word pc, 1171) (a, 1024)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST mldsa_nttunpack_tmc) /\
              read RIP s = word pc /\
              C_ARGUMENTS [a] s /\
              read (memory :> bytes(a, 1024)) s = num_of_wordlist l)
         (\s. read RIP s = word (pc + 1170) /\
              (LENGTH l = 256
               ==> read (memory :> bytes(a, 1024)) s =
                   num_of_wordlist (unpack_nttunpack l)))
         (MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes(a, 1024)] ,,
          MAYCHANGE [RIP] ,,
          MAYCHANGE [ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10; ZMM11])`,
  
  MAP_EVERY X_GEN_TAC [`a:int64`; `l:int32 list`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  
  ASM_CASES_TAC `LENGTH(l:int32 list) = 256` THENL
   [ASM_REWRITE_TAC[] THEN ENSURES_INIT_TAC "s0";
    X86_SIM_TAC MLDSA_NTTUNPACK_TMC_EXEC (1--192)] THEN
  
  UNDISCH_TAC
   `read(memory :> bytes(a,1024)) s0 = num_of_wordlist(l:int32 list)` THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
   [GSYM LIST_OF_SEQ_EQ_SELF] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(RAND_CONV(RAND_CONV LIST_OF_SEQ_CONV))) THEN
  REWRITE_TAC[] THEN
  
  (* Pair int32 values into 256-bit words for AVX2 operations *)
  REPLICATE_TAC 3
   (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
         [GSYM NUM_OF_PAIR_WORDLIST]) THEN
  REWRITE_TAC[pair_wordlist] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  REWRITE_TAC[GSYM BYTES256_WBYTES] THEN STRIP_TAC THEN
  
  (* Step through each instruction with SIMD simplification *)
  MAP_EVERY (fun n ->
    X86_STEPS_TAC MLDSA_NTTUNPACK_TMC_EXEC [n] THEN
    SIMD_SIMPLIFY_TAC[])
   (1--192) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  
  (* Extract all the memory writes from the execution *)
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
    CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
    check (can (term_match [] `read qqq s:int256 = xxx`) o concl))) THEN
  
  (* Expand memory representation and verify against specification *)
  REWRITE_TAC[ARITH_RULE `1024 = 8 * 128`] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN
  REWRITE_TAC[unpack_nttunpack; nttunpack_unorder] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[num_of_wordlist; VAL] THEN
  
  REWRITE_TAC[bignum_of_wordlist; VAL] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  CONV_TAC(TOP_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV
   (BIT_WORD_CONV ORELSEC
    GEN_REWRITE_CONV I [BITVAL_CLAUSES; OR_CLAUSES; AND_CLAUSES])) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ABBREV_TAC `two = &2:real` THEN REAL_ARITH_TAC);;

let MLDSA_NTTUNPACK_NOIBT_SUBROUTINE_CORRECT = prove
 (`!a (l:int32 list) pc stackpointer returnaddress.
  aligned 32 a /\
  nonoverlapping (word pc, LENGTH mldsa_nttunpack_tmc) (a, 1024) /\
  nonoverlapping (stackpointer, 8) (a, 1024)
  ==> ensures x86
       (\s. bytes_loaded s (word pc) mldsa_nttunpack_tmc /\
            read RIP s = word pc /\
            read RSP s = stackpointer /\
            read (memory :> bytes64 stackpointer) s = returnaddress /\
            C_ARGUMENTS [a] s /\
            read (memory :> bytes(a, 1024)) s = num_of_wordlist l)
       (\s. read RIP s = returnaddress /\
            read RSP s = word_add stackpointer (word 8) /\
            (LENGTH l = 256
             ==> read (memory :> bytes(a, 1024)) s =
                 num_of_wordlist (unpack_nttunpack l)))
       (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [memory :> bytes(a, 1024)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mldsa_nttunpack_tmc MLDSA_NTTUNPACK_CORRECT);;

let MLDSA_NTTUNPACK_SUBROUTINE_CORRECT = prove
 (`!a (l:int32 list) pc stackpointer returnaddress.
  aligned 32 a /\
  nonoverlapping (word pc, LENGTH mldsa_nttunpack_mc) (a, 1024) /\
  nonoverlapping (stackpointer, 8) (a, 1024)
  ==> ensures x86
       (\s. bytes_loaded s (word pc) mldsa_nttunpack_mc /\
            read RIP s = word pc /\
            read RSP s = stackpointer /\
            read (memory :> bytes64 stackpointer) s = returnaddress /\
            C_ARGUMENTS [a] s /\
            read (memory :> bytes(a, 1024)) s = num_of_wordlist l)
       (\s. read RIP s = returnaddress /\
            read RSP s = word_add stackpointer (word 8) /\
            (LENGTH l = 256
             ==> read (memory :> bytes(a, 1024)) s =
                 num_of_wordlist (unpack_nttunpack l)))
       (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [memory :> bytes(a, 1024)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_NTTUNPACK_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version                                        *)
(* ------------------------------------------------------------------------- *)

let mldsa_nttunpack_windows_mc = define_from_elf
   "mldsa_nttunpack_windows_mc" "x86/mldsa/mldsa_nttunpack.obj";;

let mldsa_nttunpack_windows_tmc =
  define_trimmed "mldsa_nttunpack_windows_tmc" mldsa_nttunpack_windows_mc;;

let MLDSA_NTTUNPACK_WINDOWS_TMC_EXEC =
  X86_MK_EXEC_RULE mldsa_nttunpack_windows_tmc;;

let MLDSA_NTTUNPACK_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!a (l:int32 list) pc stackpointer returnaddress.
    aligned 32 a /\
    nonoverlapping (word pc, LENGTH mldsa_nttunpack_windows_tmc) (a, 1024) /\
    nonoverlapping (word_sub stackpointer (word 176), 184) (a, 1024) /\
    nonoverlapping (word pc, LENGTH mldsa_nttunpack_windows_tmc)
                   (word_sub stackpointer (word 176), 176)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mldsa_nttunpack_windows_tmc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              WINDOWS_C_ARGUMENTS [a] s /\
              read (memory :> bytes(a, 1024)) s = num_of_wordlist l)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              (LENGTH l = 256
               ==> read (memory :> bytes(a, 1024)) s =
                   num_of_wordlist (unpack_nttunpack l)))
         (MAYCHANGE [RSP] ,,
          MAYCHANGE [memory :> bytes(a, 1024)] ,,
          WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(word_sub stackpointer (word 176), 176)])`,
  
  REPLICATE_TAC 3 GEN_TAC THEN
  WORD_FORALL_OFFSET_TAC 176 THEN
  REPEAT GEN_TAC THEN

  REWRITE_TAC[fst MLDSA_NTTUNPACK_WINDOWS_TMC_EXEC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[WINDOWS_C_ARGUMENTS] THEN
  REWRITE_TAC[WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN

  ENSURES_PRESERVED_TAC "rdi_init" `RDI` THEN
  ENSURES_PRESERVED_TAC "init_xmm6" `ZMM6 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm7" `ZMM7 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm8" `ZMM8 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm9" `ZMM9 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm10" `ZMM10 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm11" `ZMM11 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm12" `ZMM12 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm13" `ZMM13 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm14" `ZMM14 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm15" `ZMM15 :> bottomhalf :> bottomhalf` THEN

  REWRITE_TAC[READ_ZMM_BOTTOM_QUARTER'] THEN
  REWRITE_TAC(map GSYM
    [YMM6;YMM7;YMM8;YMM9;YMM10;YMM11;YMM12;YMM13;YMM14;YMM15]) THEN

  GHOST_INTRO_TAC `init_ymm6:int256` `read YMM6` THEN
  GHOST_INTRO_TAC `init_ymm7:int256` `read YMM7` THEN
  GHOST_INTRO_TAC `init_ymm8:int256` `read YMM8` THEN
  GHOST_INTRO_TAC `init_ymm9:int256` `read YMM9` THEN
  GHOST_INTRO_TAC `init_ymm10:int256` `read YMM10` THEN
  GHOST_INTRO_TAC `init_ymm11:int256` `read YMM11` THEN
  GHOST_INTRO_TAC `init_ymm12:int256` `read YMM12` THEN
  GHOST_INTRO_TAC `init_ymm13:int256` `read YMM13` THEN
  GHOST_INTRO_TAC `init_ymm14:int256` `read YMM14` THEN
  GHOST_INTRO_TAC `init_ymm15:int256` `read YMM15` THEN

  GLOBALIZE_PRECONDITION_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN

  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLDSA_NTTUNPACK_WINDOWS_TMC_EXEC (1--13) THEN

  MP_TAC(SPECL [`a:int64`; `l:int32 list`; `pc + 81`]
    MLDSA_NTTUNPACK_CORRECT) THEN
  ASM_REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
  ANTS_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN

  X86_BIGSTEP_TAC MLDSA_NTTUNPACK_WINDOWS_TMC_EXEC "s14" THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP
     (BYTES_LOADED_SUBPROGRAM_RULE mldsa_nttunpack_windows_tmc
     (REWRITE_RULE[BUTLAST_CLAUSES]
      (AP_TERM `BUTLAST:byte list->byte list` mldsa_nttunpack_tmc))
     81));
    RULE_ASSUM_TAC(CONV_RULE(TRY_CONV RIP_PLUS_CONV))] THEN

  MAP_EVERY ABBREV_TAC
   [`ymm6_epilog = read YMM6 s14`;
    `ymm7_epilog = read YMM7 s14`;
    `ymm8_epilog = read YMM8 s14`;
    `ymm9_epilog = read YMM9 s14`;
    `ymm10_epilog = read YMM10 s14`;
    `ymm11_epilog = read YMM11 s14`;
    `ymm12_epilog = read YMM12 s14`;
    `ymm13_epilog = read YMM13 s14`;
    `ymm14_epilog = read YMM14 s14`;
    `ymm15_epilog = read YMM15 s14`] THEN

  X86_STEPS_TAC MLDSA_NTTUNPACK_WINDOWS_TMC_EXEC (15--27) THEN

  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_ZMM_QUARTER]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_YMM_SSE_QUARTER]) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

let MLDSA_NTTUNPACK_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!a (l:int32 list) pc stackpointer returnaddress.
    aligned 32 a /\
    nonoverlapping (word pc, LENGTH mldsa_nttunpack_windows_mc) (a, 1024) /\
    nonoverlapping (word_sub stackpointer (word 176), 184) (a, 1024) /\
    nonoverlapping (word pc, LENGTH mldsa_nttunpack_windows_mc)
                   (word_sub stackpointer (word 176), 176)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mldsa_nttunpack_windows_mc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              WINDOWS_C_ARGUMENTS [a] s /\
              read (memory :> bytes(a, 1024)) s = num_of_wordlist l)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              (LENGTH l = 256
               ==> read (memory :> bytes(a, 1024)) s =
                   num_of_wordlist (unpack_nttunpack l)))
         (MAYCHANGE [RSP] ,,
          MAYCHANGE [memory :> bytes(a, 1024)] ,,
          WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(word_sub stackpointer (word 176), 176)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_NTTUNPACK_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

(* ========================================================================= *)
(* Constant-time and memory safety proof.                                    *)
(* (specs generated with generate_four_variants_of_x86_safety_specs)         *)
(* ========================================================================= *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mldsa_nttunpack" subroutine_signatures)
    MLDSA_NTTUNPACK_CORRECT
    MLDSA_NTTUNPACK_TMC_EXEC;;

let MLDSA_NTTUNPACK_SAFE = time prove
 (`exists f_events.
       forall e a pc.
           aligned 32 a /\ nonoverlapping (word pc,1171) (a,1024)
           ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) (BUTLAST mldsa_nttunpack_tmc) /\
                    read RIP s = word pc /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s.
                    read RIP s = word (pc + 1170) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a pc /\
                         memaccess_inbounds e2 [a,1024; a,1024] [a,1024]))
               (MAYCHANGE [events] ,,
                MAYCHANGE [memory :> bytes (a,1024)] ,,
                MAYCHANGE [RIP] ,,
                MAYCHANGE
                [ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10; ZMM11])`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLDSA_NTTUNPACK_TMC_EXEC);;

let MLDSA_NTTUNPACK_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
    forall e a pc stackpointer returnaddress.
        aligned 32 a /\
        nonoverlapping (word pc,LENGTH mldsa_nttunpack_tmc) (a,1024) /\
        nonoverlapping (stackpointer,8) (a,1024)
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) mldsa_nttunpack_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [a] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events a pc stackpointer returnaddress /\
                      memaccess_inbounds e2 [a,1024; a,1024; stackpointer,8]
                      [a,1024; stackpointer,0]))
            (MAYCHANGE [RSP] ,,
             MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes (a,1024)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mldsa_nttunpack_tmc MLDSA_NTTUNPACK_SAFE
    THEN DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLDSA_NTTUNPACK_SUBROUTINE_SAFE = time prove
 (`exists f_events.
    forall e a pc stackpointer returnaddress.
        aligned 32 a /\
        nonoverlapping (word pc,LENGTH mldsa_nttunpack_mc) (a,1024) /\
        nonoverlapping (stackpointer,8) (a,1024)
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) mldsa_nttunpack_mc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [a] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events a pc stackpointer returnaddress /\
                      memaccess_inbounds e2 [a,1024; a,1024; stackpointer,8]
                      [a,1024; stackpointer,0]))
            (MAYCHANGE [RSP] ,,
             MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes (a,1024)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_NTTUNPACK_NOIBT_SUBROUTINE_SAFE));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof of Windows ABI version.             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NTTUNPACK_NOIBT_WINDOWS_SUBROUTINE_SAFE = time prove
 (`exists f_events.
    forall e a pc stackpointer returnaddress.
        aligned 32 a /\
        nonoverlapping (word pc,LENGTH mldsa_nttunpack_windows_tmc) (a,1024) /\
        nonoverlapping (word_sub stackpointer (word 176),184) (a,1024) /\
        nonoverlapping (word pc,LENGTH mldsa_nttunpack_windows_tmc)
        (word_sub stackpointer (word 176),176)
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) mldsa_nttunpack_windows_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 WINDOWS_C_ARGUMENTS [a] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 =
                      f_events a pc (word_sub stackpointer (word 176))
                      returnaddress /\
                      memaccess_inbounds e2
                      [a,1024; a,1024; word_sub stackpointer (word 176),184]
                      [a,1024; word_sub stackpointer (word 176),176]))
            (MAYCHANGE [RSP] ,,
             MAYCHANGE [memory :> bytes (a,1024)] ,,
             WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
             [memory :> bytes (word_sub stackpointer (word 176),176)])`,
  (* The safety property specific tactics *)
  ASSUME_CALLEE_SAFETY_TAC MLDSA_NTTUNPACK_SAFE "H_subth" THEN
  META_EXISTS_TAC THEN

  (* Copied from functional correctness *)
  REPLICATE_TAC 3 GEN_TAC THEN
  WORD_FORALL_OFFSET_TAC 176 THEN
  REPEAT GEN_TAC THEN

  REWRITE_TAC[fst MLDSA_NTTUNPACK_WINDOWS_TMC_EXEC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[WINDOWS_C_ARGUMENTS] THEN
  REWRITE_TAC[WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN

  ENSURES_PRESERVED_TAC "rdi_init" `RDI` THEN
  ENSURES_PRESERVED_TAC "init_xmm6" `ZMM6 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm7" `ZMM7 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm8" `ZMM8 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm9" `ZMM9 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm10" `ZMM10 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm11" `ZMM11 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm12" `ZMM12 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm13" `ZMM13 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm14" `ZMM14 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm15" `ZMM15 :> bottomhalf :> bottomhalf` THEN

  REWRITE_TAC[READ_ZMM_BOTTOM_QUARTER'] THEN
  REWRITE_TAC(map GSYM
    [YMM6;YMM7;YMM8;YMM9;YMM10;YMM11;YMM12;YMM13;YMM14;YMM15]) THEN

  GHOST_INTRO_TAC `init_ymm6:int256` `read YMM6` THEN
  GHOST_INTRO_TAC `init_ymm7:int256` `read YMM7` THEN
  GHOST_INTRO_TAC `init_ymm8:int256` `read YMM8` THEN
  GHOST_INTRO_TAC `init_ymm9:int256` `read YMM9` THEN
  GHOST_INTRO_TAC `init_ymm10:int256` `read YMM10` THEN
  GHOST_INTRO_TAC `init_ymm11:int256` `read YMM11` THEN
  GHOST_INTRO_TAC `init_ymm12:int256` `read YMM12` THEN
  GHOST_INTRO_TAC `init_ymm13:int256` `read YMM13` THEN
  GHOST_INTRO_TAC `init_ymm14:int256` `read YMM14` THEN
  GHOST_INTRO_TAC `init_ymm15:int256` `read YMM15` THEN

  GLOBALIZE_PRECONDITION_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN

  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLDSA_NTTUNPACK_WINDOWS_TMC_EXEC (1--13) THEN

  (* safety property version *)
  W(fun (asl,w) ->
    let current_events = List.filter_map (fun (_,ath) -> let t = concl ath in
      if is_eq t && is_read_events (lhs t) then Some (rhs t)
      else None) asl in
    if length current_events <> 1
    then failwith "More than 'read events .. = ..?'"
    else
      REMOVE_THEN "H_subth"
        (MP_TAC o SPECL [hd current_events; `a:int64`; `pc + 81`]))
  THEN
  (* coming back to the functional correctness *)
  ASM_REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
  ANTS_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN

  X86_BIGSTEP_TAC MLDSA_NTTUNPACK_WINDOWS_TMC_EXEC "s14" THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP
     (BYTES_LOADED_SUBPROGRAM_RULE mldsa_nttunpack_windows_tmc
     (REWRITE_RULE[BUTLAST_CLAUSES]
      (AP_TERM `BUTLAST:byte list->byte list` mldsa_nttunpack_tmc))
     81));
    RULE_ASSUM_TAC(CONV_RULE(TRY_CONV RIP_PLUS_CONV))] THEN

  MAP_EVERY ABBREV_TAC
   [`ymm6_epilog = read YMM6 s14`;
    `ymm7_epilog = read YMM7 s14`;
    `ymm8_epilog = read YMM8 s14`;
    `ymm9_epilog = read YMM9 s14`;
    `ymm10_epilog = read YMM10 s14`;
    `ymm11_epilog = read YMM11 s14`;
    `ymm12_epilog = read YMM12 s14`;
    `ymm13_epilog = read YMM13 s14`;
    `ymm14_epilog = read YMM14 s14`;
    `ymm15_epilog = read YMM15 s14`] THEN

  X86_STEPS_TAC MLDSA_NTTUNPACK_WINDOWS_TMC_EXEC (15--27) THEN

  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_ZMM_QUARTER]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_YMM_SSE_QUARTER]) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (* safety property specific *)
  CONJ_TAC THENL [ DISCHARGE_SAFETY_PROPERTY_TAC; ALL_TAC ] THEN
  (* functional correctness *)
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

let MLDSA_NTTUNPACK_WINDOWS_SUBROUTINE_SAFE = time prove
 (`exists f_events.
    forall e a pc stackpointer returnaddress.
        aligned 32 a /\
        nonoverlapping (word pc,LENGTH mldsa_nttunpack_windows_mc) (a,1024) /\
        nonoverlapping (word_sub stackpointer (word 176),184) (a,1024) /\
        nonoverlapping (word pc,LENGTH mldsa_nttunpack_windows_mc)
        (word_sub stackpointer (word 176),176)
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) mldsa_nttunpack_windows_mc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 WINDOWS_C_ARGUMENTS [a] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 =
                      f_events a pc (word_sub stackpointer (word 176))
                      returnaddress /\
                      memaccess_inbounds e2
                      [a,1024; a,1024; word_sub stackpointer (word 176),184]
                      [a,1024; word_sub stackpointer (word 176),176]))
            (MAYCHANGE [RSP] ,,
             MAYCHANGE [memory :> bytes (a,1024)] ,,
             WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
             [memory :> bytes (word_sub stackpointer (word 176),176)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_NTTUNPACK_NOIBT_WINDOWS_SUBROUTINE_SAFE));;
