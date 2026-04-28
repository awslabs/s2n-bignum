(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conditional addition of Q to polynomial coefficients for ML-DSA (looped). *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(**** print_literal_from_elf "x86/mldsa/mldsa_caddq.o";;
 ****)

let mldsa_caddq_mc = define_assert_from_elf "mldsa_caddq_mc" "x86/mldsa/mldsa_caddq.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xba; 0x01; 0xe0; 0x7f; 0x00;
                           (* MOV (% edx) (Imm32 (word 8380417)) *)
  0x48; 0x8d; 0x87; 0x00; 0x04; 0x00; 0x00;
                           (* LEA (% rax) (%% (rdi,1024)) *)
  0xc5; 0xe9; 0xef; 0xd2;  (* VPXOR (%_% xmm2) (%_% xmm2) (%_% xmm2) *)
  0xc5; 0xf9; 0x6e; 0xca;  (* VMOVD (%_% xmm1) (% edx) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc9;
                           (* VPBROADCASTD (%_% ymm1) (%_% xmm1) *)
  0xc5; 0xed; 0x66; 0x07;  (* VPCMPGTD (%_% ymm0) (%_% ymm2) (Memop Word256 (%% (rdi,0))) *)
  0xc5; 0xfd; 0xdb; 0xc1;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xfd; 0xfe; 0x07;  (* VPADDD (%_% ymm0) (%_% ymm0) (Memop Word256 (%% (rdi,0))) *)
  0xc5; 0xfd; 0x7f; 0x07;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm0) *)
  0xc5; 0xed; 0x66; 0x5f; 0x20;
                           (* VPCMPGTD (%_% ymm3) (%_% ymm2) (Memop Word256 (%% (rdi,32))) *)
  0xc5; 0xe5; 0xdb; 0xd9;  (* VPAND (%_% ymm3) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0xe5; 0xfe; 0x5f; 0x20;
                           (* VPADDD (%_% ymm3) (%_% ymm3) (Memop Word256 (%% (rdi,32))) *)
  0xc5; 0xfd; 0x7f; 0x5f; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm3) *)
  0xc5; 0xed; 0x66; 0x67; 0x40;
                           (* VPCMPGTD (%_% ymm4) (%_% ymm2) (Memop Word256 (%% (rdi,64))) *)
  0xc5; 0xdd; 0xdb; 0xe1;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xfe; 0x67; 0x40;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (Memop Word256 (%% (rdi,64))) *)
  0xc5; 0xfd; 0x7f; 0x67; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rdi,64))) (%_% ymm4) *)
  0xc5; 0xed; 0x66; 0x6f; 0x60;
                           (* VPCMPGTD (%_% ymm5) (%_% ymm2) (Memop Word256 (%% (rdi,96))) *)
  0xc5; 0xd5; 0xdb; 0xe9;  (* VPAND (%_% ymm5) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0xd5; 0xfe; 0x6f; 0x60;
                           (* VPADDD (%_% ymm5) (%_% ymm5) (Memop Word256 (%% (rdi,96))) *)
  0xc5; 0xfd; 0x7f; 0x6f; 0x60;
                           (* VMOVDQA (Memop Word256 (%% (rdi,96))) (%_% ymm5) *)
  0x48; 0x81; 0xc7; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% rdi) (Imm32 (word 128)) *)
  0x48; 0x39; 0xf8;        (* CMP (% rax) (% rdi) *)
  0x75; 0xab;              (* JNE (Imm8 (word 171)) *)
  0xc3                     (* RET *)
];;

let mldsa_caddq_tmc = define_trimmed "mldsa_caddq_tmc" mldsa_caddq_mc;;
let MLDSA_CADDQ_TMC_EXEC = X86_MK_CORE_EXEC_RULE mldsa_caddq_tmc;;

(* ------------------------------------------------------------------------- *)
(* Functional specification of caddq                                         *)
(* ------------------------------------------------------------------------- *)

(* The x86 caddq computes: word_add x (word_and (if word_igt 0 x then 0xffffffff else 0) Q)
   This is equivalent to: if ival x < 0 then x + Q else x *)
let mldsa_caddq = define
 `(mldsa_caddq:int32->int32) x =
   word_add x
    (word_and
      (if word_igt (word 0:int32) x then word 0xffffffff else word 0)
      (word 8380417))`;;

let mldsa_caddq_direct = prove
 (`!x:int32.
    ival(mldsa_caddq x) =
    if ival x < &0 then ival x + &8380417 else ival x`,
  REWRITE_TAC[mldsa_caddq] THEN BITBLAST_TAC);;

let mldsa_caddq_rem = prove
 (`!x:int32. abs(ival x) < &8380417
    ==> ival(mldsa_caddq x) = ival x rem &8380417`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mldsa_caddq_direct] THEN
  COND_CASES_TAC THENL [
    ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    REWRITE_TAC[INT_REM_UNIQUE] THEN
    CONV_TAC INT_REDUCE_CONV THEN
    CONJ_TAC THENL [ASM_INT_ARITH_TAC; CONV_TAC INTEGER_RULE];
    MATCH_MP_TAC(GSYM INT_REM_LT) THEN
    ASM_INT_ARITH_TAC
  ]);;

(* The YMM1 constant: Q = 8380417 broadcast to all 8 lanes *)
let ymm1_q_val = define
 `ymm1_q_val:int256 =
  word 225935595421087293402315996791205668696012104344015382954355885915737415681`;;

(* ------------------------------------------------------------------------- *)
(* Core correctness theorem                                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_CADDQ_CORRECT = prove
 (`!a x pc.
        aligned 32 a /\
        nonoverlapping (word pc,LENGTH mldsa_caddq_tmc) (a, 1024)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_caddq_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [a] s /\
                  (!i. i < 256
                      ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                          x i) /\
                  (!i. i < 256 ==> abs(ival(x i)) < &8380417))
             (\s. read RIP s = word(pc + 110) /\
                  !i. i < 256
                      ==> ival(read(memory :> bytes32
                                 (word_add a (word(4 * i)))) s) =
                          ival(x i) rem &8380417)
             (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5] ,,
              MAYCHANGE [RAX; RDI] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bytes(a,1024)])`,

  MAP_EVERY X_GEN_TAC [`a:int64`; `x:num->int32`; `pc:num`] THEN

  REWRITE_TAC[NONOVERLAPPING_CLAUSES; C_ARGUMENTS; fst MLDSA_CADDQ_TMC_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Expand the precondition foralls into individual assumptions ***)

  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN

  REWRITE_TAC [SOME_FLAGS; fst MLDSA_CADDQ_TMC_EXEC] THEN

  (*** Set up the loop with ENSURES_WHILE_PAUP_TAC ***)
  (*** 8 iterations, loop body at pc+25, back-edge (JNE) at pc+108 ***)

  ENSURES_WHILE_PAUP_TAC `0` `8` `pc + 25` `pc + 108`
   `\i s.
      (read RAX s = word_add a (word 1024) /\
       read RDI s = word_add a (word(128 * i)) /\
       read YMM1 s = ymm1_q_val /\
       read YMM2 s = (word 0:int256) /\
       (!j. j < 32 * i
            ==> read(memory :> bytes32
                    (word_add a (word(4 * j)))) s = mldsa_caddq(x j)) /\
       (!j. 32 * i <= j /\ j < 256
            ==> read(memory :> bytes32
                    (word_add a (word(4 * j)))) s = x j)) /\
      (read ZF s <=> i = 8)` THEN

  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  [
    (*** Preamble: 5 instructions (MOV edx, LEA rax, VPXOR, VMOVD, VPBROADCASTD) ***)
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLDSA_CADDQ_TMC_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_0; WORD_ADD_0; LT; LE_0; ymm1_q_val] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    ASM_REWRITE_TAC[];

    (*** Loop body preservation: handled below ***)
    ALL_TAC;

    (*** Back-edge: JNE jumps back when i < 8 ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    X86_SIM_TAC MLDSA_CADDQ_TMC_EXEC [1];

    (*** Exit: JNE falls through when i = 8, reach pc+110 ***)
    X86_SIM_TAC MLDSA_CADDQ_TMC_EXEC [1] THEN
    REWRITE_TAC[ARITH_RULE `32 * 8 = 256`] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC mldsa_caddq_rem THEN
    ASM_REWRITE_TAC[]
  ] THEN

  (*** The main loop body: 18 instructions per iteration ***)
  (*** From pc+25 with inv[i], execute body to pc+108 establishing inv[i+1] ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN

  (*** Case split on i to get concrete offsets for memory merge/split ***)

  SUBGOAL_THEN
   `i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/
    i = 4 \/ i = 5 \/ i = 6 \/ i = 7`
  MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH]) THEN

  (*** Expand the foralls in the precondition of the ensures body ***)
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN (

  (*** Ghost the YMM registers that will be overwritten ***)
  GHOST_INTRO_TAC `init_ymm0:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `init_ymm3:int256` `read YMM3` THEN
  GHOST_INTRO_TAC `init_ymm4:int256` `read YMM4` THEN
  GHOST_INTRO_TAC `init_ymm5:int256` `read YMM5` THEN

  ENSURES_INIT_TAC "s0" THEN

  (*** Merge 4 bytes256 at the current base offset ***)

  MP_TAC(end_itlist CONJ (map (fun n -> READ_MEMORY_MERGE_CONV 3
              (subst[mk_small_numeral(32*n),`n:num`]
                    `read (memory :> bytes256
                       (word_add (read RDI s0) (word n))) s0`))
              (0--3))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS
    [`read (memory :> bytes32 a) s = x`] THEN
  STRIP_TAC THEN

  (*** Step through the 18 instructions with SIMD simplification ***)
  MAP_EVERY (fun n ->
      X86_STEPS_TAC MLDSA_CADDQ_TMC_EXEC [n] THEN
      SIMD_SIMPLIFY_TAC[mldsa_caddq])
             (1--18) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Split bytes256 results back to bytes32 ***)
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
     CONV_RULE(SIMD_SIMPLIFY_CONV[mldsa_caddq]) o
     CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
     check (can (term_match [] `read qqq s18:int256 = xxx`) o concl))) THEN

  (*** Prove the postcondition: expand foralls and rewrite ***)
  CONV_TAC(EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_ADD_SYM] THEN
  REWRITE_TAC[GSYM mldsa_caddq] THEN
  REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_ACCEPT_TAC));;

let MLDSA_CADDQ_NOIBT_SUBROUTINE_CORRECT = prove
 (`!a x pc stackpointer returnaddress.
        aligned 32 a /\
        nonoverlapping (word pc,LENGTH mldsa_caddq_tmc) (a,1024) /\
        nonoverlapping (stackpointer,8) (a,1024)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_caddq_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  (!i. i < 256
                      ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                          x i) /\
                  (!i. i < 256 ==> abs(ival(x i)) < &8380417))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> ival(read(memory :> bytes32
                                 (word_add a (word(4 * i)))) s) =
                          ival(x i) rem &8380417)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mldsa_caddq_tmc MLDSA_CADDQ_CORRECT);;

let MLDSA_CADDQ_SUBROUTINE_CORRECT = prove
 (`!a x pc stackpointer returnaddress.
        aligned 32 a /\
        nonoverlapping (word pc,LENGTH mldsa_caddq_mc) (a,1024) /\
        nonoverlapping (stackpointer,8) (a,1024)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_caddq_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  (!i. i < 256
                      ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                          x i) /\
                  (!i. i < 256 ==> abs(ival(x i)) < &8380417))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> ival(read(memory :> bytes32
                                 (word_add a (word(4 * i)))) s) =
                          ival(x i) rem &8380417)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_CADDQ_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let mldsa_caddq_windows_mc = define_from_elf
   "mldsa_caddq_windows_mc" "x86/mldsa/mldsa_caddq.obj";;

let mldsa_caddq_windows_tmc =
  define_trimmed "mldsa_caddq_windows_tmc" mldsa_caddq_windows_mc;;

let MLDSA_CADDQ_WINDOWS_TMC_EXEC =
  X86_MK_EXEC_RULE mldsa_caddq_windows_tmc;;

let MLDSA_CADDQ_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!a x pc stackpointer returnaddress.
        aligned 32 a /\
        nonoverlapping (word pc,LENGTH mldsa_caddq_windows_tmc) (a,1024) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (a,1024) /\
        nonoverlapping (word pc,LENGTH mldsa_caddq_windows_tmc)
                       (word_sub stackpointer (word 16),16)
        ==> ensures x86
              (\s. bytes_loaded s (word pc) mldsa_caddq_windows_tmc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   WINDOWS_C_ARGUMENTS [a] s /\
                   (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                           x i) /\
                   (!i. i < 256 ==> abs(ival(x i)) < &8380417))
              (\s. read RIP s = returnaddress /\
                   read RSP s = word_add stackpointer (word 8) /\
                   !i. i < 256
                       ==> ival(read(memory :> bytes32
                                  (word_add a (word(4 * i)))) s) =
                           ival(x i) rem &8380417)
              (MAYCHANGE [RSP] ,,
               WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)] ,,
               MAYCHANGE [memory :> bytes(a,1024)])`,
  REPLICATE_TAC 3 GEN_TAC THEN
  WORD_FORALL_OFFSET_TAC 16 THEN REPEAT GEN_TAC THEN

  REWRITE_TAC[fst MLDSA_CADDQ_WINDOWS_TMC_EXEC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[WINDOWS_C_ARGUMENTS] THEN
  REWRITE_TAC[WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN

  ENSURES_PRESERVED_TAC "rdi_init" `RDI` THEN

  GLOBALIZE_PRECONDITION_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN

  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLDSA_CADDQ_WINDOWS_TMC_EXEC (1--3) THEN

  MP_TAC(SPECL [`a:int64`; `x:num->int32`; `pc + 19`]
    MLDSA_CADDQ_CORRECT) THEN
  ASM_REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
  ANTS_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN

  X86_BIGSTEP_TAC MLDSA_CADDQ_WINDOWS_TMC_EXEC "s4" THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP
     (BYTES_LOADED_SUBPROGRAM_RULE mldsa_caddq_windows_tmc
     (REWRITE_RULE[BUTLAST_CLAUSES]
      (AP_TERM `BUTLAST:byte list->byte list` mldsa_caddq_tmc))
     19));
    RULE_ASSUM_TAC(CONV_RULE(TRY_CONV RIP_PLUS_CONV))] THEN

  X86_STEPS_TAC MLDSA_CADDQ_WINDOWS_TMC_EXEC (5--6) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

let MLDSA_CADDQ_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!a x pc stackpointer returnaddress.
        aligned 32 a /\
        nonoverlapping (word pc,LENGTH mldsa_caddq_windows_mc) (a,1024) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (a,1024) /\
        nonoverlapping (word pc,LENGTH mldsa_caddq_windows_mc)
                       (word_sub stackpointer (word 16),16)
        ==> ensures x86
              (\s. bytes_loaded s (word pc) mldsa_caddq_windows_mc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   WINDOWS_C_ARGUMENTS [a] s /\
                   (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                           x i) /\
                   (!i. i < 256 ==> abs(ival(x i)) < &8380417))
              (\s. read RIP s = returnaddress /\
                   read RSP s = word_add stackpointer (word 8) /\
                   !i. i < 256
                       ==> ival(read(memory :> bytes32
                                  (word_add a (word(4 * i)))) s) =
                           ival(x i) rem &8380417)
              (MAYCHANGE [RSP] ,,
               WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)] ,,
               MAYCHANGE [memory :> bytes(a,1024)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_CADDQ_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mldsa_caddq" subroutine_signatures)
    MLDSA_CADDQ_CORRECT
    MLDSA_CADDQ_TMC_EXEC;;

let MLDSA_CADDQ_SAFE =
  REWRITE_RULE [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SOME_FLAGS]
  (time prove
   (full_spec,
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SOME_FLAGS] THEN
    PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars
      MLDSA_CADDQ_TMC_EXEC));;

let MLDSA_CADDQ_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a pc stackpointer returnaddress.
          aligned 32 a /\
          nonoverlapping (word pc, LENGTH mldsa_caddq_tmc) (a, 1024) /\
          nonoverlapping (stackpointer, 8) (a, 1024)
          ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mldsa_caddq_tmc /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a pc stackpointer returnaddress /\
                         memaccess_inbounds e2 [a,1024; stackpointer,8]
                                               [a,1024; stackpointer,8]))
               (\s s'. true)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mldsa_caddq_tmc MLDSA_CADDQ_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLDSA_CADDQ_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a pc stackpointer returnaddress.
          aligned 32 a /\
          nonoverlapping (word pc, LENGTH mldsa_caddq_mc) (a, 1024) /\
          nonoverlapping (stackpointer, 8) (a, 1024)
          ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mldsa_caddq_mc /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a pc stackpointer returnaddress /\
                         memaccess_inbounds e2 [a,1024; stackpointer,8]
                                               [a,1024; stackpointer,8]))
               (\s s'. true)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_CADDQ_NOIBT_SUBROUTINE_SAFE));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof of Windows ABI version.             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_CADDQ_NOIBT_WINDOWS_SUBROUTINE_SAFE = prove
 (`exists f_events. forall e a pc stackpointer returnaddress.
        aligned 32 a /\
        nonoverlapping (word pc, LENGTH mldsa_caddq_windows_tmc) (a, 1024) /\
        nonoverlapping (word_sub stackpointer (word 176), 184) (a, 1024) /\
        nonoverlapping (word pc, LENGTH mldsa_caddq_windows_tmc)
                       (word_sub stackpointer (word 176), 176)
        ==> ensures x86
              (\s.
                  bytes_loaded s (word pc) mldsa_caddq_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [a] s /\
                  read events s = e)
              (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a pc (word_sub stackpointer (word 176)) returnaddress /\
                        memaccess_inbounds e2
                          [a,1024; word_sub stackpointer (word 176),184]
                          [a,1024; word_sub stackpointer (word 176),184]))
              (MAYCHANGE [RSP] ,,
               WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [memory :> bytes(word_sub stackpointer (word 176), 176)] ,,
               MAYCHANGE [memory :> bytes(a, 1024)])`,
  ASSUME_CALLEE_SAFETY_TAC MLDSA_CADDQ_SAFE "H_subth" THEN
  META_EXISTS_TAC THEN

  REPLICATE_TAC 3 GEN_TAC THEN
  WORD_FORALL_OFFSET_TAC 176 THEN
  REPEAT GEN_TAC THEN

  REWRITE_TAC[fst MLDSA_CADDQ_WINDOWS_TMC_EXEC] THEN
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
  X86_STEPS_TAC MLDSA_CADDQ_WINDOWS_TMC_EXEC (1--13) THEN

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
  ASM_REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
  ANTS_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN

  X86_BIGSTEP_TAC MLDSA_CADDQ_WINDOWS_TMC_EXEC "s14" THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP
     (BYTES_LOADED_SUBPROGRAM_RULE mldsa_caddq_windows_tmc
     (REWRITE_RULE[BUTLAST_CLAUSES]
      (AP_TERM `BUTLAST:byte list->byte list` mldsa_caddq_tmc))
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

  X86_STEPS_TAC MLDSA_CADDQ_WINDOWS_TMC_EXEC (15--27) THEN

  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_ZMM_QUARTER]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_YMM_SSE_QUARTER]) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ DISCHARGE_SAFETY_PROPERTY_TAC; ALL_TAC ] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

let MLDSA_CADDQ_WINDOWS_SUBROUTINE_SAFE = prove
 (`exists f_events. forall e a pc stackpointer returnaddress.
        aligned 32 a /\
        nonoverlapping (word pc, LENGTH mldsa_caddq_windows_mc) (a, 1024) /\
        nonoverlapping (word_sub stackpointer (word 176), 184) (a, 1024) /\
        nonoverlapping (word pc, LENGTH mldsa_caddq_windows_mc)
                       (word_sub stackpointer (word 176), 176)
        ==> ensures x86
              (\s.
                  bytes_loaded s (word pc) mldsa_caddq_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [a] s /\
                  read events s = e)
              (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a pc (word_sub stackpointer (word 176)) returnaddress /\
                        memaccess_inbounds e2
                          [a,1024; word_sub stackpointer (word 176),184]
                          [a,1024; word_sub stackpointer (word 176),184]))
              (MAYCHANGE [RSP] ,,
               WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [memory :> bytes(word_sub stackpointer (word 176), 176)] ,,
               MAYCHANGE [memory :> bytes(a, 1024)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_CADDQ_NOIBT_WINDOWS_SUBROUTINE_SAFE));;
