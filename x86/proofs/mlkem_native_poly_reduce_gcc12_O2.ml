(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction of polynomial coefficients producing nonnegative remainders.    *)
(* This is the code for mlkem_poly_reduce from mlkem-native's portable C     *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md).  *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/mlkem_native.ml";;

(**** print_literal_from_elf
        "x86/mlkem_native/mlkem_native_poly_reduce_gcc12_O2.o";;
 ****)

let mlkem_native_poly_reduce_gcc12_O2_mc = define_assert_from_elf
  "mlkem_native_poly_reduce_gcc12_O2_mc"
  "x86/mlkem_native/mlkem_native_poly_reduce_gcc12_O2.o"
[
  0x48; 0x89; 0xf9;        (* MOV (% rcx) (% rdi) *)
  0x48; 0x8d; 0xb7; 0x00; 0x02; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rdi,512)) *)
  0x66; 0x0f; 0x1f; 0x44; 0x00; 0x00;
                           (* NOP_N (Memop Word (%%% (rax,0,rax))) *)
  0x0f; 0xbf; 0x11;        (* MOVSX (% edx) (Memop Word (%% (rcx,0))) *)
  0x89; 0xd0;              (* MOV (% eax) (% edx) *)
  0x69; 0xd2; 0xbf; 0x4e; 0x00; 0x00;
                           (* IMUL3 (% edx) (% edx,Imm32 (word 20159)) *)
  0x81; 0xc2; 0x00; 0x00; 0x00; 0x02;
                           (* ADD (% edx) (Imm32 (word 33554432)) *)
  0xc1; 0xfa; 0x1a;        (* SAR (% edx) (Imm8 (word 26)) *)
  0x66; 0x69; 0xd2; 0xff; 0xf2;
                           (* IMUL3 (% dx) (% dx,Imm16 (word 62207)) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x0f; 0xbf; 0xc2;        (* MOVSX (% eax) (% dx) *)
  0xc1; 0xe8; 0x10;        (* SHR (% eax) (Imm8 (word 16)) *)
  0xf7; 0xd8;              (* NEG (% eax) *)
  0x8d; 0xba; 0x01; 0x0d; 0x00; 0x00;
                           (* LEA (% edi) (%% (rdx,3329)) *)
  0xc1; 0xf8; 0x10;        (* SAR (% eax) (Imm8 (word 16)) *)
  0x48; 0x83; 0xc1; 0x02;  (* ADD (% rcx) (Imm8 (word 2)) *)
  0x31; 0xd7;              (* XOR (% edi) (% edx) *)
  0x21; 0xf8;              (* AND (% eax) (% edi) *)
  0x31; 0xd0;              (* XOR (% eax) (% edx) *)
  0x66; 0x89; 0x41; 0xfe;  (* MOV (Memop Word (%% (rcx,18446744073709551614)))
                                  (% ax) *)
  0x48; 0x39; 0xf1;        (* CMP (% rcx) (% rsi) *)
  0x75; 0xc1;              (* JNE (Imm8 (word 193)) *)
  0xc3                     (* RET *)
];;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_EXEC =
  X86_MK_EXEC_RULE mlkem_native_poly_reduce_gcc12_O2_mc;;

(* ------------------------------------------------------------------------- *)
(* The value computed for each coefficient.                                  *)
(* ------------------------------------------------------------------------- *)

(*** The Barrett reduction as compiled: the quotient t is computed in a
 *** 32-bit register and its bottom 16 bits multiplied by -3329 in the
 *** 16-bit one, the product p, then the input is added as 32 bits r. Only
 *** the bottom 16 bits of r matter, and they are the reduction "barred".
 ***)

let BARRETT_GCC12_O2 = prove
 (`!(x:int16) (t:int32) (p:int16).
     word_zx(word_add
              (word_zx (word_join
                          (word_subword (word_zx t:int64) (16,48):48 word)
                          p:int64):int32)
              (word_sx x:int32)):int16 =
     word_add x p`,
  BITBLAST_TAC);;

(*** The conditional addition of 3329, mlk_scalar_signed_to_unsigned_q,
 *** as compiled, applied to the 32-bit result r of the Barrett reduction
 ***)

let CONDADD_GCC12_O2 = prove
 (`!r:int32.
     word_zx
      (word_xor
        (word_and
          (word_ishr
            (word_neg (word_ushr (word_sx (word_zx r:int16):int32) 16)) 16)
          (word_xor (word_sx (word_add (word_zx r:int64) (word 3329)):int32)
                    r))
        r):int16 =
     let w = word_zx r:int16 in
     word_add w (word_and (word_ishr w 15) (word 3329))`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_CORRECT = prove
 (`!a x pc.
        nonoverlapping (word pc,0x50) (a,512)
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_poly_reduce_gcc12_O2_mc /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read RIP s = word(pc + 0x4f) /\
                  !i. i < 256
                      ==> ival(read(memory :> bytes16
                                 (word_add a (word(2 * i)))) s) =
                          ival(x i) rem &3329)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,512)])`,
  MAP_EVERY X_GEN_TAC [`a:int64`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `256` `pc + 0x10` `pc + 0x4a`
   `\i s. read RCX s = word_add a (word(2 * i)) /\
          read RSI s = word_add a (word 512) /\
          (!j. j < i
               ==> ival(read(memory :> bytes16(word_add a (word(2 * j)))) s) =
                   ival(x j) rem &3329) /\
          (!j. i <= j /\ j < 256
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   x j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization of the pointers ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; CONJUNCT1 LT; LE_0] THEN
    ASM_REWRITE_TAC[];

    (*** The loop body: process one coefficient ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `read (memory :> bytes16 (word_add a (word (2 * i)))) s0 = x i /\
      (!j. i + 1 <= j /\ j < 256
           ==> read (memory :> bytes16 (word_add a (word (2 * j)))) s0 = x j)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ALL_TAC; GEN_TAC THEN STRIP_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_EXEC (1--17) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `2 * (i + 1) = 2 * i + 2`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN
    REWRITE_TAC[ARITH_RULE `j < i + 1 <=> j < i \/ j = i`] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MLKEM_NATIVE_WORD_SIMP_TAC THEN
    REWRITE_TAC[CONDADD_GCC12_O2] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[BARRETT_GCC12_O2; BARRED_GCC12_O2; BARRED_CONDADD_REM];

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_EXEC (1--2) THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_add a (word (2 * i)))
                     (word_add a (word 512)):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[WORD_RULE
       `word_sub (word_add a x) (word_add a y) = word_sub x y`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 256 ==> 2 * i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `i < 256` THEN ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SUBROUTINE_CORRECT = prove
 (`!a x pc stackpointer returnaddress.
        nonoverlapping (word pc,0x50) (a,512) /\
        nonoverlapping (stackpointer,8) (a,512)
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_poly_reduce_gcc12_O2_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> ival(read(memory :> bytes16
                                 (word_add a (word(2 * i)))) s) =
                          ival(x i) rem &3329)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,512)])`,
  X86_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_EXEC
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

(*** The C signature is the same as that of mlkem_reduce ***)

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_reduce" subroutine_signatures)
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_CORRECT
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_EXEC;;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SAFE = time prove
 (`exists f_events.
       forall e a pc.
           nonoverlapping (word pc,0x50) (a,512)
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_poly_reduce_gcc12_O2_mc /\
                    read RIP s = word pc /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s. read RIP s = word (pc + 0x4f) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a pc /\
                         memaccess_inbounds e2 [a,512] [a,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,512)])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (pc:num).
      APPEND
        (f_ev_epil a pc)
        (APPEND
          (ENUMERATEL 256 (\i. f_ev_loop a pc i))
          (f_ev_prol a pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `256` `pc + 0x10` `pc + 0x4f`
    `\i s. read RCX s = word_add a (word(2 * i)) /\
           read RSI s = word_add a (word 512)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_EXEC (1--3) THEN
    CONJ_TAC THENL [REWRITE_TAC[MULT_0; WORD_ADD_0]; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_EXEC (1--0) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_EXEC (1--19) THEN
  SUBGOAL_THEN
   `~(val(word_add (word_add a (word (2 * i))) (word 2):int64) =
      val(word_add a (word 512):int64)) <=> i + 1 < 256`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_EQ; GSYM WORD_ADD_ASSOC; WORD_ADD_LCANCEL_EQ] THEN
    REWRITE_TAC[GSYM WORD_ADD; WORD_EQ; DIMINDEX_64; CONG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 256 ==> 2 * i + 2 < 18446744073709551616`] THEN
    UNDISCH_TAC `i < 256` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 * (i + 1) = 2 * i + 2`] THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a pc stackpointer returnaddress.
           nonoverlapping (word pc,0x50) (a,512) /\
           nonoverlapping (stackpointer,8) (a,512)
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_poly_reduce_gcc12_O2_mc /\
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
                         memaccess_inbounds e2 [a,512; stackpointer,8]
                                               [a,512]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,512)])`,
  X86_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_EXEC
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The same code in the whole image, at address 0x5660 (see                  *)
(* mlkem_native_libmlkem_gcc12_O2.ml).                                       *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IN_IMAGE =
  MLKEM_NATIVE_IMAGE_CODE_RULE mlkem_native_poly_reduce_gcc12_O2_mc
    0x5660 [];;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!a x pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        nonoverlapping (word pc,0x82a0) (a,512) /\
        nonoverlapping (stackpointer,8) (a,512)
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x5660) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> ival(read(memory :> bytes16
                                 (word_add a (word(2 * i)))) s) =
                          ival(x i) rem &3329)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,512)])`,
  MLKEM_NATIVE_IMAGE_TAC
   (INST [`pc + 0x5660`,`pc:num`]
     (SPEC_ALL MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SUBROUTINE_CORRECT))
   [MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IN_IMAGE]);;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (`exists f_events.
       forall e a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           nonoverlapping (word pc,0x82a0) (a,512) /\
           nonoverlapping (stackpointer,8) (a,512)
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x5660) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a pc stackpointer returnaddress /\
                         memaccess_inbounds e2 [a,512; stackpointer,8]
                                               [a,512]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,512)])`,
  MLKEM_NATIVE_IMAGE_SAFE_TAC MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SUBROUTINE_SAFE
   [`pc + 0x5660`,`pc:num`]
   [MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IN_IMAGE]);;
